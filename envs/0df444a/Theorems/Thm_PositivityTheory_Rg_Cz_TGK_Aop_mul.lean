-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_Aop_mul
-- name    : PositivityTheory.Rg.Cz.TGK.Aop_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:57.619555+00:00
-- url     : https://prove2.me/theorems/6f81e639-925e-4e0d-ae6f-a6714934ebd5
-- title:
--   TGK: Aop mul
-- statement:
--   The TGK construction uses the Aop mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L52-L63

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

theorem PositivityTheory.Rg.Cz.TGK.Aop_mul (K L : P → Matrix (Fin n) (Fin n) ℂ) :
    (Aop (fun q => K q * L q) : Module.End ℂ (TV n M P)) = Aop K * Aop L := by sorry
