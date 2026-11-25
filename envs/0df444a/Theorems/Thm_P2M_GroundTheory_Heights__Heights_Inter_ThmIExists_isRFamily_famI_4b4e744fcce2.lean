-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isRFamily_famI_4b4e744fcce2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isRFamily_famI_4b4e744fcce2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:32:44.156408+00:00
-- url     : https://prove2.me/theorems/08d4e450-b810-5ec1-81ba-75e585e14d33
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists is RFamily fam I 4b4e744fcce2: P2 M Ground Theory Heights  Heights Inter Thm IExists is RFamily fam I 4b4e744fcce2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists is RFamily fam I 4b4e744fcce2 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists is RFamily fam I 4b4e744fcce2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L228-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L228-L233

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isRFamily_famI_4b4e744fcce2 (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement)
    (hstep : ∀ n, HasRAt (famI (ι := ι)) n → LastAddAt (famI (ι := ι)) n → WDAt (famI (ι := ι)) (n + 1)) :
    IsRFamily (famI (ι := ι)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«isRFamily_famI» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_isRFamily_famI_4b4e744fcce2
