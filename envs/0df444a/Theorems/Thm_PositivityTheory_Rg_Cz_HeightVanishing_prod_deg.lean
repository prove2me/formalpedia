-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_prod_deg
-- name    : PositivityTheory.Rg.Cz.HeightVanishing.prod_deg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:48.551612+00:00
-- url     : https://prove2.me/theorems/9d399b8f-af91-410c-995f-77f560d979a0
-- title:
--   Height Vanishing: prod deg
-- statement:
--   The Height Vanishing construction uses the prod deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L284-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PHeight.lean#L284-L296

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.HeightVanishing
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable (E : Fin n → Fin n → Module.End ℂ M)

theorem PositivityTheory.Rg.Cz.HeightVanishing.prod_deg (L : List ℂ) :
    Deg E L.length (L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod ∧
      Commute (Om E (0 : Fin 1)) (L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod := by sorry
