-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_tE_apply
-- name    : PositivityTheory.Rg.Cz.tE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:01.21607+00:00
-- url     : https://prove2.me/theorems/967009d2-67af-4c74-918a-bdb5df71c42a
-- title:
--   Cz: t E apply
-- statement:
--   The Cz construction uses the t E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/LiftCommEAt.lean#L24-L26

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

theorem PositivityTheory.Rg.Cz.tE_apply (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    tE S E a b f I = E a b (f I) + ∑ p ∈ S, if I p = a then f (Function.update I p b) else 0 := by sorry
