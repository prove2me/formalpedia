-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P29_invariant_fixed_test_concentration
-- name    : QAlgorithms.Papers.Independent.Extend50.P29.invariant_fixed_test_concentration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:16:09.816248+00:00
-- url     : https://prove2.me/theorems/14d1ae97-6e66-4a68-8bae-6ba0382bcd57
-- title:
--   Appendix C / Eq.(B8): concentration for fixed density-matrix tests of random invariant states
-- statement:
--   Let $G$ be a finite group, $d=|G|\ge1$, and $n\ge2$. Sample a Haar unit vector in $\mathcal H_G^{\otimes n}$ and map it by the explicit orbit isometry $M$ to a normalized invariant vector $\Psi$ on $n+1$ regular registers. For each fixed positive semidefinite trace-one matrix $\sigma$ on registers $0,1$, put
--   $$P_{\delta,\sigma}=\Pr\left[\left|\operatorname{Tr}\!\left(\sigma(\Psi_{01}-I/d^2)\right)\right|\ge\delta/d^2\right],\qquad P_\delta=\sup_\sigma P_{\delta,\sigma}.$$
--   For every $0\le\delta\le1$, the printed Eq.(B8) asserts
--   $$P_\delta\le\exp\left(-d^{n-2}\delta^2/6\right).$$
--   This is a two-sided deviation bound for every fixed test. The endpoints are included, and the supremum is outside the sampling event.
--
--   **Formalization Note** The one-sided estimates in Appendix C directly give a factor-two union bound; the source does not explicitly remove that prefactor. The exact printed target is retained as a statement with this proof concern disclosed, not certified as a proved result.
-- source:
--   Error Correction of Quantum Reference Frame Information, arXiv:1709.04471v1, PDF p. 13, Appendix C / Eq.(B8): concentration for fixed density-matrix tests of random invariant states

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P29

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)

open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)

/-- PDF p.13, Eq.(B8), proved in Appendix C pp.13--15: printed two-sided
tail bound. Its missing-prefactor proof concern is recorded in MODERATION_NOTES;
no prefactor or extra interior-domain restriction is silently inserted. n=r+2. -/
theorem invariant_fixed_test_concentration
    (G : Type) [Group G] [Fintype G] (r : ℕ)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    worstTestTail G r δ ≤ Real.exp (-(Fintype.card G : ℝ) ^ r * δ ^ 2 / 6) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P29

end
