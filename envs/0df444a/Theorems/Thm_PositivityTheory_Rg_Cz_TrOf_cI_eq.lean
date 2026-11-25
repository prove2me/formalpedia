-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TrOf_cI_eq
-- name    : PositivityTheory.Rg.Cz.TrOf.cI_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:26.436048+00:00
-- url     : https://prove2.me/theorems/a8957f82-7475-4e53-be5c-a2cb7acf56e8
-- title:
--   Tr Of: c I eq
-- statement:
--   The Tr Of construction uses the c I eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L140-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransOf.lean#L140-L141

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

theorem PositivityTheory.Rg.Cz.TrOf.cI_eq {C : Type} [DecidableEq C] (col : P → C) (p q : P) : cI col p = cI col q ↔ col p = col q := by sorry
