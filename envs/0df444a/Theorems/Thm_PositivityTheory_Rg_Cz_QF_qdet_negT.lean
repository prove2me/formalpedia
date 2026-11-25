-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_QF_qdet_negT
-- name    : PositivityTheory.Rg.Cz.QF.qdet_negT
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:27.501131+00:00
-- url     : https://prove2.me/theorems/7a60e294-5262-433b-8f8f-7aefb5d3122e
-- title:
--   QF: qdet neg T
-- statement:
--   The QF construction uses the qdet neg T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PQdetFacts.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PQdetFacts.lean#L46-L48

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.QF
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem PositivityTheory.Rg.Cz.QF.qdet_negT {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ) :
    qdet (fun a b => -E b a) u = (-1) ^ n * qdet E ((n : ℂ) - 1 - u) := by sorry
