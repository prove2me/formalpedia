-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_merge_upd_right
-- name    : PositivityTheory.Rg.Cz.TA.merge_upd_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:35.862499+00:00
-- url     : https://prove2.me/theorems/c071dc7c-7a99-5125-9a1d-a64afe406a11
-- title:
--   TA: merge upd right
-- statement:
--   The TA construction uses the merge upd right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllB.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllB.lean#L37-L47

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
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
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]
omit [Fintype P]

theorem PositivityTheory.Rg.Cz.TA.merge_upd_right (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // ¬ q p}) (c : Fin n) :
    merge q J (Function.update I x c) = Function.update (merge q J I) x.1 c := by sorry
