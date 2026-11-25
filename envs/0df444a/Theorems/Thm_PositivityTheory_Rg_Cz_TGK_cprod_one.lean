-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_cprod_one
-- name    : PositivityTheory.Rg.Cz.TGK.cprod_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:43.487114+00:00
-- url     : https://prove2.me/theorems/0f0bda43-e5c3-40d6-8410-da2c1bd4aa97
-- title:
--   TGK: cprod one
-- statement:
--   The TGK construction uses the cprod one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKC.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKC.lean#L20-L25

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
omit [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TGK.cprod_one (I J : P → Fin n) :
    ∏ p, (1 : Matrix (Fin n) (Fin n) ℂ) (I p) (J p) = if I = J then 1 else 0 := by sorry
