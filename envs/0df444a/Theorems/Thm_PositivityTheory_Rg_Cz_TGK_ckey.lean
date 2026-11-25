-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_ckey
-- name    : PositivityTheory.Rg.Cz.TGK.ckey
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:44.641797+00:00
-- url     : https://prove2.me/theorems/a632f20b-cecf-557e-8269-3913c2d09301
-- title:
--   TGK: ckey
-- statement:
--   The TGK construction uses the ckey property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKC.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKC.lean#L55-L63

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKC
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TGK.ckey (I : P → Fin n) (S : Finset P) (F : Fin n → Fin n → ℂ) (h : Fin n → P → ℂ) :
    ∑ a, ∑ b, F a b * ∑ p ∈ S, (if I p = a then h b p else 0) = ∑ p ∈ S, ∑ b, F (I p) b * h b p := by sorry
