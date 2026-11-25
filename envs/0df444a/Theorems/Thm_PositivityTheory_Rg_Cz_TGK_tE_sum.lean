-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_tE_sum
-- name    : PositivityTheory.Rg.Cz.TGK.tE_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:00.006286+00:00
-- url     : https://prove2.me/theorems/6bfc0336-4f28-433f-b53e-a1d32e436fc5
-- title:
--   TGK: t E sum
-- statement:
--   The TGK construction uses the t E sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L189-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L189-L202

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
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

theorem PositivityTheory.Rg.Cz.TGK.tE_sum (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (k : Fin n → Fin n → ℂ) :
    ∑ c, ∑ d, k c d • tE S E c d =
      lift (∑ c, ∑ d, k c d • E c d) + ∑ p ∈ S, mAt p (∑ c, ∑ d, k c d • Matrix.single c d (1 : ℂ)) := by sorry
