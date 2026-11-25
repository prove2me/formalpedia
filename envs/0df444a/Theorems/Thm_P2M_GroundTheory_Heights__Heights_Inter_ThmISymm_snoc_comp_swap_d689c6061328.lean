-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_snoc_comp_swap_d689c6061328
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_snoc_comp_swap_d689c6061328
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:20.848977+00:00
-- url     : https://prove2.me/theorems/9c15f814-5cb2-43d3-97bc-4fc7c3417138
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm ISymm snoc comp swap d689c6061328: P2 M Ground Theory Heights  Heights Inter Thm ISymm snoc comp swap d689c6061328
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm ISymm snoc comp swap d689c6061328 construction uses the P2 M Ground Theory Heights  Heights Inter Thm ISymm snoc comp swap d689c6061328 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L198-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PThmISymm.lean#L198-L210

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_snoc_comp_swap_d689c6061328 {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (a b : Fin n) :
    (Fin.snoc L A : Fin (n + 1) → HermLine ι) ∘ Equiv.swap a.castSucc b.castSucc =
      Fin.snoc (L ∘ Equiv.swap a b) A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmISymm».«snoc_comp_swap» := P2M_GroundTheory_Heights__Heights_Inter_ThmISymm_snoc_comp_swap_d689c6061328
