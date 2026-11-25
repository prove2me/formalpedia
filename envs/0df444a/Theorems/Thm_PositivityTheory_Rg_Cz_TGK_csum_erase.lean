-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_csum_erase
-- name    : PositivityTheory.Rg.Cz.TGK.csum_erase
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:52.284365+00:00
-- url     : https://prove2.me/theorems/36c82409-460f-5243-bce8-b4057e38719d
-- title:
--   TGK: csum erase
-- statement:
--   The TGK construction uses the csum erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKC.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKC.lean#L46-L52

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

theorem PositivityTheory.Rg.Cz.TGK.csum_erase (I : P → Fin n) (p : P) (φ : (P → Fin n) → ℂ) :
    ∑ J, (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) * φ J =
      ∑ b, φ (Function.update I p b) := by sorry
