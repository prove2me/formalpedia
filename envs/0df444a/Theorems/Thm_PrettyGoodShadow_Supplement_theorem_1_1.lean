-- Prove2me | Theorems.Thm_PrettyGoodShadow_Supplement_theorem_1_1
-- name    : PrettyGoodShadow.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:02:09.208797+00:00
-- url     : https://prove2.me/theorems/8dafea3b-8b27-4843-8382-56e44b111f34
-- title:
--   Theorem 1.1 — worst-case, dimension-free shadow tomography with $O(\log(2m)\log(m/\delta)/\varepsilon^2)$ copies (corrected: $\log m\to\log 2m$)
-- statement:
--   This is the main theorem of the paper: shadow tomography can be solved with a number of copies that does not depend on the dimension.
--
--   In the **shadow tomography problem** one is given copies of an unknown $d$-dimensional quantum state $\rho$ together with known observables $O_1,\dots,O_m$, Hermitian with operator norm $\|O_i\|_\infty\le1$, and must estimate every expectation value $\operatorname{tr}(O_i\rho)$ to within $\pm\varepsilon$ with total failure probability at most $\delta$. An algorithm on $n$ copies is a POVM $\{N_z\}_{z\in Z}$ with finitely many outcomes acting on $\rho^{\otimes n}$, together with a decoder $g:Z\to\mathbb R^m$ that turns the outcome into the predictions $\hat o=g(z)$.
--
--   There is an absolute constant $C>0$ such that the following holds for every dimension $d$, every $m\ge1$, all Hermitian $O_1,\dots,O_m$ with $\|O_i\|_\infty\le1$ and all $\varepsilon,\delta>0$. For every integer
--
--   $$
--   n\ \ge\ C\,\frac{\log(2m)\,\log(m/\delta)}{\varepsilon^2}
--   $$
--
--   there are a POVM $\{N_z\}$ on $n$ copies and a decoder $g$, chosen before the state, such that for **every** density matrix $\rho$,
--
--   $$
--   \Pr_{z\sim\{\operatorname{tr}(N_z\rho^{\otimes n})\}}\Big[\max_{i\in[m]}\big|g_i(z)-\operatorname{tr}(O_i\rho)\big|\le\varepsilon\Big]\ \ge\ 1-\delta .
--   $$
--
--   Previous algorithms used a number of copies growing with $\log d$; this bound depends only on $m$, $\varepsilon$ and $\delta$, and it is within a factor $\log(2m)$ of the known lower bound $\Omega(\log(m/\delta)/\varepsilon^2)$. The paper obtains it from its average-case Theorem 4.2 (the goal of this mission) through the minimax theorem.
--
--   **Formalization Note** The constant $C$ is chosen before the dimension, the observables, $\varepsilon$ and $\delta$. The measurement and the decoder do not depend on $\rho$, and the guarantee holds for every density matrix, with no prior and no finite family of states. Outcome probabilities are $\operatorname{Re}\operatorname{tr}(N_z\rho^{\otimes n})$, and expectation values are $\operatorname{Re}\operatorname{tr}(O_i\rho)$ (the published `PrettyGoodShadow.obs`). Natural logarithm; the norm is the $L^2$ operator norm. The decoder may take any value in $\mathbb R^m$. The number of copies may exceed the bound (unused copies are ignored) and may be $0$, in which case the POVM acts on a one-point space. The small cases stay in the statement and are true: for $\varepsilon\ge1$ the constant output $0$ succeeds, and when the bound is below $1$ (only possible for $m=1$ with $\delta$ close to $1$, or for $\delta\ge m$) a uniform guess on a grid of spacing $2\varepsilon$ succeeds with probability at least $\varepsilon/(1+2\varepsilon)$ for every state, which exceeds $1-\delta$ once $C$ is large enough.
--
--   Differences from the source:
--   - correction: O(log(m) log(m/δ)/ε²) copies → C log(2m) log(m/δ)/ε² copies; reason: the printed rate is 0 at m = 1, which is false. Counterexample satisfying every assumption of the source: d = 2, m = 1, O = Z, ε = 1/2, δ = 1/4. A 0-copy POVM has an outcome law independent of ρ, and the success sets for ρ = |0⟩⟨0| (tr(Zρ) = 1) and ρ = |1⟩⟨1| (tr(Zρ) = −1) are disjoint at ε = 1/2, so one of the two states succeeds with probability ≤ 1/2 < 3/4. For m ≥ 2 the two rates agree up to a factor 2
--   - encoding: O(·) copies → one absolute constant C chosen before d, m, O, ε, δ, and every n ≥ C log(2m) log(m/δ)/ε²; reason: this is the meaning of O(·) with an absolute constant; extra copies can be ignored
--   - encoding: "an algorithm" for the shadow tomography problem → a finite-outcome POVM on (ℂ^d)^{⊗n} and a decoder Z → ℝ^m, both fixed before ρ, succeeding for every density matrix ρ; reason: §2.2, p.7 specifies an algorithm as a POVM whose outcomes are the predictions ô ∈ ℝ^m; grouping the effects N_z by the value g(z) gives such a POVM, so the Lean algorithm is one in the source's sense (the finite-outcome requirement only restricts the algorithm, so the Lean claim implies the source's); the problem of p.3 asks for success on the unknown state, i.e. on every state
--   - encoding: observables O_1, …, O_m (normalization printed in Problem 4.1, p.17, and Conjecture 2.1, p.8) → Hermitian O_i with ‖O_i‖ ≤ 1 in the L² operator norm, and hypothesis 1 ≤ m; reason: ‖·‖∞ is the operator norm; log(m) is undefined at m = 0 and with no observables the problem is degenerate
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Theorem 1.1, p.28 (stated p.3); problem statement §1, p.3; algorithms as POVMs with predictions in ℝ^m, §2.2, p.7; normalization ‖O_i‖∞ ≤ 1, Problem 4.1, p.17

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_PrettyGoodShadow_obs

open scoped Matrix.Norms.L2Operator

namespace PrettyGoodShadow.Supplement

open ShadowTomography.UpperBound (tensorPow)

/-- **Theorem 1.1, worst-case dimension-free shadow tomography, with `log m` corrected to `log(2m)`**
(Grewal, Pelecanos, Spilecki, Tang, Wright, *Pretty good shadow tomography*, arXiv:2610.06781, sha256 bd055b7d…,
Theorem 1.1, p.28, stated p.3; problem statement §1, p.3; algorithms as POVMs with predictions in `ℝ^m`, §2.2, p.7).
There is an absolute constant `C > 0` such that, for every dimension `d`, every `m ≥ 1`, every family of Hermitian
observables `O_1, …, O_m` with `‖O_i‖_∞ ≤ 1` and every `ε, δ > 0`, for every number of copies
`n ≥ C log(2m) log(m/δ)/ε²` there are one finite-outcome POVM `{N_z}` on `n` copies and one decoder `g`, both chosen
before the state, such that for **every** density matrix `ρ`, measuring `ρ^{⊗n}` and outputting `g(z)` estimates every
`tr(O_i ρ)` to within `±ε` with probability at least `1 − δ`.

**Formalization Note** `C` is chosen before `d`, `m`, the observables, `ε` and `δ` (dimension-free). The POVM and the
decoder are chosen before `ρ`; there is no prior and no finite family of states. The outcome probability of `z` is
`Re tr(N_z ρ^{⊗n})`. Natural logarithm; the norm is the `L²` operator norm (`Matrix.Norms.L2Operator`), so
`‖O_i‖ ≤ 1` is `‖O_i‖_∞ ≤ 1`. The decoder takes values in `ℝ^m`, unrestricted. `n` may exceed the bound (unused copies
are ignored) and may be `0`, in which case the POVM acts on a one-point space; small cases (`ε > 1`, or `m = 1` with
`δ` close to `1`) are solved by a fixed or uniformly guessed output and stay in the statement. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d : Type} [Fintype d] [DecidableEq d] (m : ℕ), 1 ≤ m →
        ∀ O : Fin m → Matrix d d ℂ, (∀ i, (O i).IsHermitian) → (∀ i, ‖O i‖ ≤ 1) →
        ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        ∀ n : ℕ, C * Real.log (2 * (m : ℝ)) * Real.log ((m : ℝ) / δ) / ε ^ 2 ≤ (n : ℝ) →
          ∃ (Z : Type) (_ : Fintype Z) (N : Z → Matrix (Fin n → d) (Fin n → d) ℂ)
            (g : Z → Fin m → ℝ), QAlgorithms.IsPOVM N ∧
            ∀ ρ : Matrix d d ℂ, WildeQIT.IsDensityOperator ρ →
              1 - δ ≤ ∑ z with (∀ i, |g z i - PrettyGoodShadow.obs (O i) ρ| ≤ ε),
                (N z * tensorPow ρ n).trace.re := by sorry

end PrettyGoodShadow.Supplement
