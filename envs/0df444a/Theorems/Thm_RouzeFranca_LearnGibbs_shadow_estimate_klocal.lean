-- Prove2me | Theorems.Thm_RouzeFranca_LearnGibbs_shadow_estimate_klocal
-- name    : RouzeFranca.LearnGibbs.shadow_estimate_klocal
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:52.234614+00:00
-- url     : https://prove2.me/theorems/b9f4871a-1062-4904-968d-64589d4c51f0
-- title:
--   Eq. (45) — $O(4^k\log(m/\delta)\epsilon^{-2})$ copies estimate all $k$-local expectations to accuracy $\epsilon$
-- statement:
--   Let $E_1,\dots,E_m$ ($m\ge1$) be Hermitian, $k$-local observables on $n$ qubits with $\|E_i\|_\infty\le1$, let $\epsilon>0$ and $\delta\in(0,1)$. There is a universal constant $C>0$ such that, whenever
--   $$
--   N\ \ge\ C\,\frac{4^k\log(m/\delta)}{\epsilon^2},
--   $$
--   there are a POVM $M$ on one copy and an estimator $\hat e:\{1,\dots,K\}^N\to\mathbb R^m$ with the following property: for **every** state $\rho$, if $M$ is applied independently to $N$ copies of $\rho$, then with probability at least $1-\delta$
--   $$
--   \bigl|\hat e_i(x)-\operatorname{tr}[E_i\rho]\bigr|\le\epsilon\quad\text{for all } i=1,\dots,m .
--   $$
--
--   This is Step 1 of the learning algorithm, in which the expectation values $e(\lambda)$ of the unknown Gibbs state are estimated; it is the source of the factor $4^k\log(m/\delta)$ in the main theorem.
--
--   **Formalization Note** $\|E_i\|_\infty$ is the operator norm. The protocol $(M,\hat e)$ is fixed before the state.
--
--   Differences from the source:
--   - generalization: estimate of e(λ) for the Gibbs state σ(λ) of linearly independent E_i → estimate of (tr[E_i ρ])_i for every state ρ, no linear independence; reason: the cited shadow method [40] works for every state; the source's case is ρ = σ(λ)
--   - reading: O(4^k log(mδ^{-1}) ϵ^{-2}) copies → ∃ C > 0 universal, N ≥ C 4^k log(m/δ)/ε²; reason: the O(·) constant is independent of every parameter
--   - reading: copies of σ(λ) → one POVM applied independently to each copy, i.i.d. outcomes, deterministic estimator chosen before the state; reason: the stronger of the possible readings; shadow tomography measures copies one at a time, and randomness is part of the outcome
--   - encoding: ∥e′(λ) − e(λ)∥_ℓp ≤ m^{1/p} ϵ → |ê_i − tr[E_i ρ]| ≤ ε for all i; reason: p = ∞ is this bound and it implies every p; same statement
--   - encoding: operators on n qubits, ∥E_i∥_∞ → complex matrices indexed by Fin n → Bool, ℓ² operator norm, real parts of traces; reason: Lean conventions; same instances
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, App. C, Eq. (45), p. 26

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs
import Definitions.Def_RouzeFranca_LearnGibbs_IsKLocal
import Definitions.Def_RouzeFranca_LearnGibbs_iidProb

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RouzeFranca.LearnGibbs

/-- **Eq. (45) (shadow estimates of k-local expectations).** There is a universal constant `C > 0`
such that for any `m ≥ 1` Hermitian, `k`-local observables `E₁, …, E_m` on `n` qubits with
`‖Eᵢ‖∞ ≤ 1`, any accuracy `ε > 0` and failure probability `δ ∈ (0, 1)`, and any number of copies
`N ≥ C · 4^k log(m/δ) / ε²`, there is a single-copy POVM `M` and an estimator `est` of the `N`
i.i.d. outcomes such that for **every** state `ρ`, with probability at least `1 − δ`,
`|est(x)ᵢ − tr[Eᵢ ρ]| ≤ ε` for all `i` simultaneously.

Rouzé, Stilck França, *Learning quantum many-body systems from a few copies*,
arXiv:2107.03333v4, App. C, Eq. (45), p. 26: "given E1, …, Em assumed to be at most k-local, with
probability at least 1 − δ we can obtain an estimate e′(λ) of e(λ) satisfying
∥e′(λ) − e(λ)∥_ℓp ≤ m^{1/p} ϵ (45) using O(4^k log(mδ^{-1}) ϵ^{-2}) copies of σ(λ)."

**Formalization Note.** `O(·)` is read as a universal constant `C`, independent of every
parameter. The ℓ_p bound `m^{1/p} ε` for all `p` is equivalent to the ℓ∞ bound `ε` written here.
The state is arbitrary (the paper applies (45) to `σ(λ)`; the cited method [40] works for every
state); the linear independence of the `Eᵢ` is not needed. The measurement is one POVM applied
to each copy independently (`iidProb`), and the protocol is chosen before the state.
`‖Eᵢ‖` is the ℓ² operator norm. -/
theorem shadow_estimate_klocal :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k m : ℕ) (E : Fin m → Mat n), 0 < m →
      (∀ i, (E i).IsHermitian) → (∀ i, ‖E i‖ ≤ 1) → (∀ i, IsKLocal k (E i)) →
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ → δ < 1 →
    ∀ N : ℕ, C * 4 ^ k * Real.log (m / δ) / ε ^ 2 ≤ N →
    ∃ (K : ℕ) (M : Fin K → Mat n) (est : (Fin N → Fin K) → Fin m → ℝ), IsPOVM M ∧
      ∀ ρ : Mat n, WildeQIT.IsDensityOperator ρ →
        1 - δ ≤ iidProb M ρ N (fun x => ∀ i, |est x i - (trace (E i * ρ)).re| ≤ ε) := by sorry

end RouzeFranca.LearnGibbs
