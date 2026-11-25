-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_LieInverse_exists_ne_of_ne_one
-- name    : PositivityTheory.Rg.Cz.LieInverse.exists_ne_of_ne_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:59.115683+00:00
-- url     : https://prove2.me/theorems/7e450e83-7747-573a-a6cc-22416735a68e
-- title:
--   Lie Inverse: exists ne of ne one
-- statement:
--   The Lie Inverse construction uses the exists ne of ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PLieInv.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PLieInv.lean#L11-L23

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PLieInv
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
open PositivityTheory.Rg.Cz.LieInverse

theorem PositivityTheory.Rg.Cz.LieInverse.exists_ne_of_ne_one {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) (i : Fin n) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by sorry
