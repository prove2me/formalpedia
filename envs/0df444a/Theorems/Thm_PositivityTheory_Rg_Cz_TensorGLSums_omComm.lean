-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TensorGLSums_omComm
-- name    : PositivityTheory.Rg.Cz.TensorGLSums.omComm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:29.977698+00:00
-- url     : https://prove2.me/theorems/cb2ca4d0-038d-496b-8857-0e3d50b8d3bd
-- title:
--   Tensor GLSums: om Comm
-- statement:
--   The Tensor GLSums construction uses the om Comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGl.lean#L38-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGl.lean#L38-L69

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGl
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
open PositivityTheory.Rg.Cz.TensorGLSums

theorem PositivityTheory.Rg.Cz.TensorGLSums.omComm {R : Type*} [Ring R] {n : ℕ} (L e : Fin n → Fin n → R) (hL : GlRel L)
    (hLe : ∀ a b c d, Commute (L a b) (e c d)) (he : ∀ a b c d, e a b * e c d = if b = c then e a d else 0)
    (c d : Fin n) : Commute (∑ a, ∑ b, L a b * e b a) (L c d + e c d) := by sorry
