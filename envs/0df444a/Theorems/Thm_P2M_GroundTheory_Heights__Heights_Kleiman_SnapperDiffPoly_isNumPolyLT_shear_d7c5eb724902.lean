-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_shear_d7c5eb724902
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_shear_d7c5eb724902
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:41.33186+00:00
-- url     : https://prove2.me/theorems/cbbf8ea7-dab5-4a11-bc79-5e02e25fe68b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly is Num Poly LT shear d7c5eb724902: P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly is Num Poly LT shear d7c5eb724902
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly is Num Poly LT shear d7c5eb724902 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly is Num Poly LT shear d7c5eb724902 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L71-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L71-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_shear_d7c5eb724902 {t D : ℕ} (ν : Fin t → ℤ) {F : (Fin t → ℕ) → ℤ → ℚ} (hF : IsNumPolyLT t D F) :
    IsNumPolyLT t D (fun n c => F n (c + ∑ i, ν i * (n i : ℤ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperDiffPoly».«isNumPolyLT_shear» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_shear_d7c5eb724902
