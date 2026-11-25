-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TrOf_tE_rl
-- name    : PositivityTheory.Rg.Cz.TrOf.tE_rl
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:48:38.950715+00:00
-- url     : https://prove2.me/theorems/c5432991-796f-4fe6-884f-1679675c29e9
-- title:
--   Tr Of: t E rl
-- statement:
--   The Tr Of construction uses the t E rl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L26-L33

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf
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
open PositivityTheory.Rg.Cz.TrOf
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

theorem PositivityTheory.Rg.Cz.TrOf.tE_rl (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) :
    tE Finset.univ E a b (rl e f) = rl e (tE Finset.univ E a b f) := by sorry
