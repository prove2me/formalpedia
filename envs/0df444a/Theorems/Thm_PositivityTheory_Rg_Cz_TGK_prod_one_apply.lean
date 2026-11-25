-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_prod_one_apply
-- name    : PositivityTheory.Rg.Cz.TGK.prod_one_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:01.428749+00:00
-- url     : https://prove2.me/theorems/293cec3d-4421-41bc-96a5-4d1aabc8a164
-- title:
--   TGK: prod one apply
-- statement:
--   The TGK construction uses the prod one apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L40-L45

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

theorem PositivityTheory.Rg.Cz.TGK.prod_one_apply (I J : P → Fin n) :
    ∏ q, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q) = if I = J then 1 else 0 := by sorry
