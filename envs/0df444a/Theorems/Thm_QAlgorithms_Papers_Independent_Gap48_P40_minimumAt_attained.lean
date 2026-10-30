-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_minimumAt_attained
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.minimumAt_attained
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-29T00:09:57.243251+00:00
-- url     : https://prove2.me/theorems/14ccd208-0220-4b85-91f1-e3d2c1894330
-- title:
--   §VI, Eq. (21): the minimum relative entropy at fixed norm distance is attained
-- statement:
--   All matrices are $d\times d$ complex matrices. A state is a positive semidefinite matrix with trace one. $D(\rho\|\sigma)$ denotes the support-aware Umegaki relative entropy $\operatorname{Tr}\rho\log\rho-\operatorname{Tr}\rho\log\sigma$ (natural logarithms, $0\log0=0$), valued in the extended reals, with value $+\infty$ when $\ker\sigma\not\subseteq\ker\rho$. Let $d\ge2$, let $N$ be a genuine unitarily invariant norm on $d\times d$ complex matrices, let $F=\operatorname{diag}(1,-1,0,\ldots,0)$ and let $0\le T\le N(F)$. Let $m_N(T)$ be the extended infimum of $D(\rho\|\sigma)$ over all pairs of states with $N(\rho-\sigma)=T$ (the platform definition `minimumAt`; an empty set would give $+\infty$).
--
--   **Claim.** The infimum is attained: there are states $\rho,\sigma$ with $N(\rho-\sigma)=T$ and $D(\rho\|\sigma)=m_N(T)$. This includes the case $m_N(T)=+\infty$, where it says that the constraint set is nonempty.
-- source:
--   Continuity bounds on the quantum relative entropy, Audenaert–Eisert, arXiv:quant-ph/0503218v3, PDF pp. 6–7, §VI, Eq. (21)–(22) and the proof of Lemma 8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40


/-- PDF pp.6–7, §VI (Eq. (21)): for a genuine UI norm and `0 ≤ T ≤ N(F)`, the extended
infimum `minimumAt d N T` is attained by some pair of states at raw distance exactly `T`
(including the value `+∞`). -/
theorem minimumAt_attained {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N)
    (T : ℝ) (hT : 0 ≤ T ∧ T ≤ N (matrixF d)) :
    ∃ rho sigma : Mat d, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      N (rho - sigma) = T ∧ relativeEntropy rho sigma = minimumAt d N T := by
  sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
