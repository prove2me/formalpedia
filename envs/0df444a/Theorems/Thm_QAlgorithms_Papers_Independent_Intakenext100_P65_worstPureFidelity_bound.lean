-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_worstPureFidelity_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.worstPureFidelity_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:38:11.767644+00:00
-- url     : https://prove2.me/theorems/781b86b8-c31a-4a4b-bd53-c3ef873ef68a
-- title:
--   Worst-case pure-input fidelity lower bound
-- statement:
--   Let $d\ge1$ be an integer and let $\mathcal E$ be a CPTP map on a d-dimensional complex Hilbert space. For a normalized pure input $|\psi\rangle$, let $f(\psi)=\langle\psi|\mathcal E(|\psi\rangle\langle\psi|)|\psi\rangle$. Write $F_E$ for the squared overlap on a normalized maximally entangled input. The minimum over normalized pure inputs is attained, and
--
--   $$1-d\sqrt{1-F_E^2}\le\min_{\|\psi\|=1} f(\psi).$$
--
--   The factor d is outside the square root, and the displayed square of the already squared-overlap channel fidelity is preserved. This is the source's deliberately loose bound, without a sharper substituted constant.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 24, Appendix A (A2): worst-case input-output lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.24 (A2): retain the printed loose constant and square of F_E. -/
theorem worstPureFidelity_bound (d : ℕ) (hd : 0 < d)
    (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) :
    (∃ v : EuclideanSpace ℂ (Fin d), ‖v‖ = 1 ∧
      effectProb (pureDensity v) (T (pureDensity v)) = worstPureFidelity d T) ∧
    1 - (d : ℝ) * Real.sqrt (1 - (QuditFidelity.entanglementFidelity d hd T) ^ 2) ≤
      worstPureFidelity d T := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
