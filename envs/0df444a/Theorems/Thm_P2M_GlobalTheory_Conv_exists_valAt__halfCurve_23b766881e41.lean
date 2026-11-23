-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Conv_exists_valAt__halfCurve_23b766881e41
-- name    : P2M_GlobalTheory_Conv_exists_valAt__halfCurve_23b766881e41
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:22.494218+00:00
-- url     : https://prove2.me/theorems/4f0cf651-0a4d-4848-915e-f22ba2b63e67
-- title:
--   P2 M Global Theory Conv exists val At  half Curve 23b766881e41: P2 M Global Theory Conv exists val At  half Curve 23b766881e41
-- statement:
--   The P2 M Global Theory Conv exists val At  half Curve 23b766881e41 construction uses the P2 M Global Theory Conv exists val At  half Curve 23b766881e41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L140-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L140-L159

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

theorem P2M_GlobalTheory_Conv_exists_valAt__halfCurve_23b766881e41 {T : ℝ} {yT : Sp (halfRing T) ⟶ Z} {y : Sp convLaurent ⟶ Z}
    (hy : spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y) {U : Z.Opens}
    (hU : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ T' ≥ T, (∀ w : ℂ, T' < w.im → ⊤ ≤ halfCurve yT w ⁻¹ᵁ U) ∧
      ∀ f : Γ(Z, U), ∃ hf : ((valR y U f : convLaurent) : ℂ⸨X⸩) ∈ halfRing T',
        ∀ (w : ℂ) (hw : T' < w.im), valAt' (halfCurve yT w) U f = ev T' w hw ⟨_, hf⟩ := by sorry

alias «GlobalTheory».«Conv».«exists_valAt'_halfCurve» := P2M_GlobalTheory_Conv_exists_valAt__halfCurve_23b766881e41
