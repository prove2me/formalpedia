-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TrOf_conj_tE
-- name    : PositivityTheory.Rg.Cz.TrOf.conj_tE
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:37.576463+00:00
-- url     : https://prove2.me/theorems/1cb3b6cf-1aa9-49da-b4e7-046855be055c
-- title:
--   Tr Of: conj t E
-- statement:
--   The Tr Of construction uses the conj t E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L35-L39

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

theorem PositivityTheory.Rg.Cz.TrOf.conj_tE (e : P ≃ Q) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    (rl (n := n) (M := M) e).conjAlgEquiv ℂ (tE Finset.univ E a b) = tE Finset.univ E a b := by sorry
