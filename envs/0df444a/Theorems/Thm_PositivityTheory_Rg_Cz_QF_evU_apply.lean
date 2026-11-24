-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_QF_evU_apply
-- name    : PositivityTheory.Rg.Cz.QF.evU_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:08.142962+00:00
-- url     : https://prove2.me/theorems/9d495b1f-d786-4df7-9bb6-dae09b58d361
-- title:
--   QF: ev U apply
-- statement:
--   The QF construction uses the ev U apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PQdetFacts.lean#L60-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PQdetFacts.lean#L60-L60

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

theorem PositivityTheory.Rg.Cz.QF.evU_apply (u : ℂ) (p : A[X]) : evU u p = eval₂ (RingHom.id A) (algebraMap ℂ A u) p := by sorry
