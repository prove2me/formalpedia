-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_Om_apply
-- name    : PositivityTheory.Rg.Cz.Om_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:43.252591+00:00
-- url     : https://prove2.me/theorems/18260da3-4f25-4a55-8fcb-a56f34224145
-- title:
--   Cz: Om apply
-- statement:
--   The Cz construction uses the Om apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L29-L37

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
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
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P]

theorem PositivityTheory.Rg.Cz.Om_apply (E : Fin n → Fin n → Module.End ℂ M) (p : P) (f : TV n M P) (I : P → Fin n) :
    Om E p f I = ∑ a, E a (I p) (f (Function.update I p a)) := by sorry
