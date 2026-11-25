-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_intCast_comp
-- name    : PositivityTheory.Rg.Cz.ChainP.intCast_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:10.948623+00:00
-- url     : https://prove2.me/theorems/4ba1291c-711b-4836-a8de-c3ff0d5b572f
-- title:
--   Chain P: int Cast comp
-- statement:
--   The Chain P construction uses the int Cast comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChainA.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChainA.lean#L14-L17

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
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
open PositivityTheory.Rg.Cz.ChainP
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem PositivityTheory.Rg.Cz.ChainP.intCast_comp (f : V →ₗ[ℂ] W) (z : ℤ) :
    f ∘ₗ ((z : Module.End ℂ V)) = ((z : Module.End ℂ W)) ∘ₗ f := by sorry
