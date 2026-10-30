-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_phasePointUncertainty
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.phasePointUncertainty
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:30:37.470661+00:00
-- url     : https://prove2.me/theorems/ab246c86-5472-4950-8b64-b268d1a4b7e9
-- title:
--   Phase-point uncertainty relation
-- statement:
--   Let $d\geq2$ be odd, possibly composite, and let $\psi$ be a normalized pure state on $n$ qudits. Write $A_x$ for the source phase-space point operators. If their three signed real expectations strictly exceed the indicated threshold, the Weyl displacements $W_{z-x}$ and $W_{y-x}$ commute.
--
--   $$
--   \operatorname{tr}(\psi A_x),\operatorname{tr}(\psi A_y),\operatorname{tr}(\psi A_z)>\sqrt{1-\frac1{2d^2}}\ \Longrightarrow\ [z-x,y-x]=0.
--   $$
--
--   This gives the source's phase-point uncertainty relation in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 60, lemma-8.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.60, Lemma 8.2: signed real expectations and a square root over the entire threshold. -/
theorem phasePointUncertainty (d n : ℕ) [NeZero d] (hd : 2 ≤ d) (hodd : Odd d)
    (v : EuclideanSpace ℂ (ResidueRegister d n)) (hv : ‖v‖ = 1) (x y z : DiscretePhaseSpace d n)
    (hx : Real.sqrt (1 - 1 / (2 * (d : ℝ) ^ 2)) <
      QAlgorithms.effectProb (phasePointOperator d n x) (QAlgorithms.pureDensity v))
    (hy : Real.sqrt (1 - 1 / (2 * (d : ℝ) ^ 2)) <
      QAlgorithms.effectProb (phasePointOperator d n y) (QAlgorithms.pureDensity v))
    (hz : Real.sqrt (1 - 1 / (2 * (d : ℝ) ^ 2)) <
      QAlgorithms.effectProb (phasePointOperator d n z) (QAlgorithms.pureDensity v)) :
    symplecticBracket (z - x) (y - x) = 0 ∧
    cyclicWeyl d n (z - x) * cyclicWeyl d n (y - x) = cyclicWeyl d n (y - x) * cyclicWeyl d n (z - x) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
