-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_WQ_glRel_of_inj
-- name    : PositivityTheory.Rg.Cz.WQ.glRel_of_inj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:03.338112+00:00
-- url     : https://prove2.me/theorems/53f31495-d69d-4cbb-bfa2-0725e0b5b584
-- title:
--   WQ: gl Rel of inj
-- statement:
--   The WQ construction uses the gl Rel of inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallQuot.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PWallQuot.lean#L30-L34

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.WQ
variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

theorem PositivityTheory.Rg.Cz.WQ.glRel_of_inj (f : A →ₐ[ℂ] B) (hf : Function.Injective f) {n : ℕ} {E : Fin n → Fin n → A}
    (h : GlRel fun a b => f (E a b)) : GlRel E := by sorry
