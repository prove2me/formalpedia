-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_snoc_56c5b29ec694
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_snoc_56c5b29ec694
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:03.405274+00:00
-- url     : https://prove2.me/theorems/e223a11a-9381-4173-80dc-b18c56971104
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists fam I snoc 56c5b29ec694: P2 M Ground Theory Heights  Heights Inter Thm IExists fam I snoc 56c5b29ec694
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists fam I snoc 56c5b29ec694 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists fam I snoc 56c5b29ec694 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L135-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L135-L143

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_snoc_56c5b29ec694 (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) :
    famI P (n + 1) (Fin.snoc L A) =
      recR famI P L (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) -
        recR famI P L (segreLine (shift A)) (secOf P fun _ => shift A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«famI_snoc» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_famI_snoc_56c5b29ec694
