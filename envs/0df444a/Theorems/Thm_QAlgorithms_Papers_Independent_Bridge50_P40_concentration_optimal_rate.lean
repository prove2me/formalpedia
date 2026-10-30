-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_concentration_optimal_rate
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.concentration_optimal_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:06:57.9461+00:00
-- url     : https://prove2.me/theorems/cf26c7fa-1391-439f-8d91-82145dce9724
-- title:
--   Optimal pure-state concentration rate and weak converse (Bennett et al.)
-- statement:
--   All registers are finite and nonempty, all source kets have unit norm, all density operators are positive semidefinite with trace one, logarithms are base two, and F denotes root fidelity. Fix a pure source $\psi^{AB}$. A feasible block pair $(r_n,f_n)$ comes from actual LOCC on $\psi^{\otimes n}$, without supplied entanglement, with target $\Phi_L$, $L\ge1$, rate $r_n=\log_2 L/n$, and root fidelity $f_n$. A rate $r$ is achievable when feasible pairs exist for every positive $n$ with $r_n\to r$ and $f_n\to1$. Then
--
--   $$\max\{r:r\text{ is achievable}\}=S(A)_\psi.$$
--
--   The maximum is an achievable asymptotic rate. For each fixed floor $c>S(A)_\psi$, there exist $\epsilon>0$ and $N$ such that every $n\ge N$, $n>0$, and every feasible pair $(r,f)$ with $r\ge c$ obey $f\le1-\epsilon$. The final printed subscript rho is interpreted as the same source Psi.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 11, Theorem 10

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.11, Theorem 10 (Bennett et al. [31]): maximum achievable pure-state
concentration yield and its weak converse. Printed: the final entropy uses
subscript rho. Changed: use Psi, the sole source of Definition 2 and the first
sentence. Why: rho there is an undefined source label, not a second state. -/
theorem concentration_optimal_rate {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : IsState psi) :
    let threshold := vnEntropy (traceRight (pureDensity psi))
    IsGreatest {rate : ℝ | SourceProtocolAchievable (ConcentrationRateFidelity psi) rate} threshold ∧
    (∀ floor : ℝ, threshold < floor → ∃ eps : ℝ, 0 < eps ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → 0 < n → ∀ rate fidelity : ℝ,
        ConcentrationRateFidelity psi n rate fidelity → floor ≤ rate →
          fidelity ≤ 1 - eps) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
