-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_JMA_xJ_mul_swap
-- name    : PositivityTheory.Rg.Cz.JMA.xJ_mul_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:58.512801+00:00
-- url     : https://prove2.me/theorems/f4906056-4a4c-48c9-b63f-22ff97989661
-- title:
--   JMA: x J mul swap
-- statement:
--   The JMA construction uses the x J mul swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L122-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L122-L125

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
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
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.JMA.xJ_mul_swap (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) : xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 := by sorry
