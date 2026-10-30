-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_merging_optimal_rate
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.merging_optimal_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:06:19.402997+00:00
-- url     : https://prove2.me/theorems/7eaa465d-9969-424d-93f3-73b4ee2bced9
-- title:
--   Optimal signed state-merging rate and weak converse (Horodecki–Oppenheim–Winter)
-- statement:
--   All registers are finite and nonempty, all source kets have unit norm, all density operators are positive semidefinite with trace one, logarithms are base two, and F denotes root fidelity. Fix a pure source $\psi^{RAB}$. For each positive block length $n$, a feasible rate-fidelity pair $(r_n,f_n)$ comes from an actual LOCC merging protocol on $\psi^{\otimes n}\otimes\Phi_K$, with arbitrary positive Schmidt ranks $K,L$, rate $r_n=(\log_2 K-\log_2 L)/n$, and complete-output root fidelity $f_n$ with the target retaining the reference and the final $\Phi_L$. A rate $r$ is achievable precisely when such pairs exist for all positive $n$, with $r_n\to r$ and $f_n\to1$. Then
--
--   $$\min\{r:r\text{ is achievable}\}=S(AB)_\psi-S(B)_\psi.$$
--
--   The minimum is attained as an achievable asymptotic rate. Positive cost consumes ebits and negative cost generates them. For every fixed ceiling $c<S(AB)_\psi-S(B)_\psi$, there exist $\epsilon>0$ and $N$ such that every $n\ge N$, $n>0$, and every feasible $(r,f)$ with $r\le c$ obey $f\le1-\epsilon$.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 8, Theorem 7 and following weak-converse paragraph

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

/-- PDF p.8, Theorem 7 (Horodecki, Oppenheim and Winter [27]) and the
following weak-converse paragraph: the minimum achievable signed cost is
S(AB)-S(B). Negative values mean generated entanglement. A fixed strictly
smaller rate ceiling bounds fidelity away from one uniformly in large blocks. -/
theorem merging_optimal_rate {A B R : Type}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi) :
    let threshold := vnEntropy (traceLeft (pureDensity psi)) -
      vnEntropy (traceLeft (traceLeft (pureDensity psi)))
    IsLeast {rate : ℝ | SourceProtocolAchievable (MergingRateFidelity psi) rate} threshold ∧
    (∀ ceiling : ℝ, ceiling < threshold → ∃ eps : ℝ, 0 < eps ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → 0 < n → ∀ rate fidelity : ℝ,
        MergingRateFidelity psi n rate fidelity → rate ≤ ceiling →
          fidelity ≤ 1 - eps) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
