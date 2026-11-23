-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Conv_valAt__halfCurve_ca595a84c520
-- name    : P2M_GlobalTheory_Conv_valAt__halfCurve_ca595a84c520
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:39.512935+00:00
-- url     : https://prove2.me/theorems/1c3615bd-833f-49a6-b267-9599eff2f1fa
-- title:
--   P2 M Global Theory Conv val At  half Curve ca595a84c520: P2 M Global Theory Conv val At  half Curve ca595a84c520
-- statement:
--   The P2 M Global Theory Conv val At  half Curve ca595a84c520 construction uses the P2 M Global Theory Conv val At  half Curve ca595a84c520 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L122-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {Z : Scheme.{0}}

theorem P2M_GlobalTheory_Conv_valAt__halfCurve_ca595a84c520 {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) {U : Z.Opens} (hU : ⊤ ≤ yT ⁻¹ᵁ U)
    {w : ℂ} (hw : T < w.im) :
    ⊤ ≤ halfCurve yT w ⁻¹ᵁ U ∧ ∀ f, valAt' (halfCurve yT w) U f = ev T w hw (valR yT U f) := by sorry

alias «GlobalTheory».«Conv».«valAt'_halfCurve» := P2M_GlobalTheory_Conv_valAt__halfCurve_ca595a84c520
