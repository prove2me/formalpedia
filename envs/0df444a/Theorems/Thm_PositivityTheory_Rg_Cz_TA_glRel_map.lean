-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_glRel_map
-- name    : PositivityTheory.Rg.Cz.TA.glRel_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:14.001031+00:00
-- url     : https://prove2.me/theorems/b6f07229-91c3-4ade-ae0a-0b09a086c701
-- title:
--   TA: gl Rel map
-- statement:
--   The TA construction uses the gl Rel map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L28-L33

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.TA.glRel_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {m : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin m → Fin m → A) (h : GlRel E) : GlRel fun a b => φ (E a b) := by sorry
