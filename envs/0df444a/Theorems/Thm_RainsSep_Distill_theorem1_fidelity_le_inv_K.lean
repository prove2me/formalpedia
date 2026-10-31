-- Prove2me | Theorems.Thm_RainsSep_Distill_theorem1_fidelity_le_inv_K
-- name    : RainsSep.Distill.theorem1_fidelity_le_inv_K
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:58:39.89517+00:00
-- url     : https://prove2.me/theorems/cfa8273c-7bf8-4483-b350-65820166157e
-- title:
--   Theorem 1: $F_{\mathcal P}(f)\le 1/K$ for $f\le\tfrac12$, and $D_*(f)=0$
-- statement:
--   Let $f$ satisfy $-\tfrac12\le f\le\tfrac12$. Then:
--
--   1. for every $n$, $K$ and every separable superoperator $\mathcal P$ from two $n$-qubit registers $V\otimes V$ to $W\otimes W$ with $\dim W=K$,
--
--   $$
--   F_{\mathcal P}(f):=F\Big(\mathcal P\big(\Delta(\tfrac43(1-f))^{\otimes n}\big)\Big)\le\frac1K ;
--   $$
--
--   2. the largest separably achievable distillation rate from $\Delta(\tfrac43(1-f))$ is $0$, i.e. $D_*(f)=0$.
--
--   This recovers the known fact that depolarized pairs of fidelity at most $1/2$ cannot be distilled, now for all separable operations.
--
--   Differences from the source:
--   - reading: for any f ≤ 1/2, with Δ((4/3)(1 − f)) "the state" of Eq. (19) → f in the range where Δ((4/3)(1 − f)) is a state, 0 ≤ f ≤ 1/2; reason: read literally over all real f ≤ 1/2 the statement is false: at f = −2, n = 1, K = 2, P(ρ) = (σx ⊗ 1)ρ(σx ⊗ 1) gives F_P = (1 − f)/3 = 1 > 1/2
--   - generalization: 0 ≤ f ≤ 1/2 → −1/2 ≤ f ≤ 1/2; reason: the paper's proof (x = 1/2 − f ≥ 0, y = 1/6 + f/3 ≥ 0) covers this range, which contains the state range; it is the largest such interval, since the same P gives F_P = (1 − f)/3 > 1/2 for every f < −1/2
--   - encoding: D∗(f) = 0, D∗ the largest achievable rate → IsGreatest of the set of achievable rates with value 0; reason: the set formulation states that 0 is achievable and is the largest; no supremum in ℝ is taken
--   - encoding: a separable superoperator has a product Kraus representation Σ_i (unspecified index set) → IsSeparableSuperop asks for a finite product Kraus family indexed by Fin m; reason: in finite dimension every separable superoperator has a finite product representation (its Choi matrix lies in the finite-dimensional separable cone, Carathéodory), so nothing is excluded
--   - encoding: V an n-qubit space, W of dimension K, an orthonormal basis, a bipartite V ⊗ V → Qubits n (bit strings of length n, false = |0⟩), W = Fin K, the first tensor factor Alice's, her qubit k paired with Bob's qubit k, computational bases, fidelity the real part of φ+† σ φ+; reason: a choice of labels: φ+ depends on the basis only up to local unitaries (p. 1), and the value is real on Hermitian operators
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Theorem 1, Eq. (36), p. 3

import Mathlib
import Definitions.Def_RainsSep_Distill_depolarizingOfFidelity
import Definitions.Def_RainsSep_Distill_AchievableSepRate

open QAlgorithms

namespace RainsSep.Distill

/-- **Theorem 1: `F_P(f) ≤ 1/K` for `f ≤ 1/2`, and `D∗(f) = 0`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Theorem 1, Eq. (36), p. 3: "Let P be a separable superoperator from V ⊗ V to W ⊗ W, where V
is an n-qubit Hilbert space, and W is a K-dimensional Hilbert space. Then for any f ≤ 1/2,
F_P(f) := F_P(∆((4/3)(1 − f))) ≤ 1/K. (36) In particular, D∗(f) = 0."

For every `f` with `−1/2 ≤ f ≤ 1/2`:
1. for every `n`, `K` and every separable superoperator `P` from `n` qubit pairs to
   `ℂ^K ⊗ ℂ^K`, `F(P(Δ((4/3)(1 − f))^{⊗n})) ≤ 1/K`;
2. `0` is the largest separably achievable rate from `Δ((4/3)(1 − f))`, i.e. `D∗(f) = 0`.

**Formalization Note.** `Δ((4/3)(1 − f))` is a state exactly for `f ∈ [0, 1]`, so the theorem's
range of states is `f ∈ [0, 1/2]`; the statement covers `[−1/2, 1/2]`. The literal "any
`f ≤ 1/2`" fails at `f = −2` (`n = 1`, `K = 2`, `P(ρ) = (σx ⊗ 1)ρ(σx ⊗ 1)` gives
`F_P = (1 − f)/3 = 1 > 1/2`). `D∗(f) = 0` is `IsGreatest` of the set of achievable rates. -/
theorem theorem1_fidelity_le_inv_K (f : ℝ) (hf0 : -1 / 2 ≤ f) (hf1 : f ≤ 1 / 2) :
    (∀ (n K : ℕ) (P : Superop (Qubits n × Qubits n) (Fin K × Fin K)), IsSeparableSuperop P →
        entFidelity (P (pairPower (depolarizingOfFidelity f) n)) ≤ 1 / (K : ℝ)) ∧
      IsGreatest {R : ℝ | AchievableSepRate (depolarizingOfFidelity f) R} 0 := by sorry

end RainsSep.Distill
