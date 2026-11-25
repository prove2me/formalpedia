-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_snoc_snoc_comp_swap_2783ae7a74db
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_snoc_snoc_comp_swap_2783ae7a74db
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:00.380917+00:00
-- url     : https://prove2.me/theorems/f5eaf872-e7c2-4aec-ada5-a38c5e48735e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm ISymm snoc snoc comp swap 2783ae7a74db: P2 M Ground Theory Heights  Heights Inter Thm ISymm snoc snoc comp swap 2783ae7a74db
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm ISymm snoc snoc comp swap 2783ae7a74db construction uses the P2 M Ground Theory Heights  Heights Inter Thm ISymm snoc snoc comp swap 2783ae7a74db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L212-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L212-L224

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmISymm
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
open GroundTheory.Heights₂.Heights.Inter.ThmISymm
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_snoc_snoc_comp_swap_2783ae7a74db {m : ℕ} (L : Fin m → HermLine ι) (X Y : HermLine ι) :
    (Fin.snoc (Fin.snoc L X) Y : Fin (m + 1 + 1) → HermLine ι) ∘
        Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1)) =
      Fin.snoc (Fin.snoc L Y) X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmISymm».«snoc_snoc_comp_swap» := P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_snoc_snoc_comp_swap_2783ae7a74db
