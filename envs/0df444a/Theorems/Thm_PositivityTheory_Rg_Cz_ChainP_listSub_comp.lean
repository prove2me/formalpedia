-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_listSub_comp
-- name    : PositivityTheory.Rg.Cz.ChainP.listSub_comp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:13.688837+00:00
-- url     : https://prove2.me/theorems/b0a90d7b-a87c-4676-aa2a-6ab87f333735
-- title:
--   Chain P: list Sub comp
-- statement:
--   The Chain P construction uses the list Sub comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChainA.lean#L48-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PChainA.lean#L48-L64

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

theorem PositivityTheory.Rg.Cz.ChainP.listSub_comp (f : V →ₗ[ℂ] W) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : f ∘ₗ A = B ∘ₗ f)
    (L : List ℂ) :
    f ∘ₗ (L.map fun r => A - algebraMap ℂ _ r).prod = (L.map fun r => B - algebraMap ℂ _ r).prod ∘ₗ f := by sorry
