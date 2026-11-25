-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TF_restrict_pow_coe
-- name    : PositivityTheory.Rg.Cz.TF.restrict_pow_coe
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:15.52237+00:00
-- url     : https://prove2.me/theorems/4f18fed4-c24e-5fd2-8ea1-c24ba8060d66
-- title:
--   TF: restrict pow coe
-- statement:
--   The TF construction uses the restrict pow coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFinCK.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFinCK.lean#L16-L21

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF

theorem PositivityTheory.Rg.Cz.TF.restrict_pow_coe {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (Z : Submodule ℂ U)
    (hZ : ∀ z ∈ Z, T z ∈ Z) : ∀ (k : ℕ) (w : Z), (((T.restrict hZ) ^ k) w : U) = (T ^ k) (w : U) := by sorry
