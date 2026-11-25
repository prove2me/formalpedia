-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eword_adjoint
-- name    : ReciprocityTheory.ChartRestriction.DS.eword_adjoint
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:55.404222+00:00
-- url     : https://prove2.me/theorems/500cc3a8-ee23-4143-b827-ae386d8adcd7
-- title:
--   DS: eword adjoint
-- statement:
--   The DS construction uses the eword adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/AnyAdj.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/AnyAdj.lean#L12-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_AnyAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.eword_adjoint {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (w : List (Fin n × Fin n)) (x y : M) :
    inner ℂ ((w.map fun p => E p.1 p.2).prod x) y =
      (w.map fun p => adjSign ε p.1 p.2).prod *
        inner ℂ x (((w.reverse.map Prod.swap).map fun p => E p.1 p.2).prod y) := by sorry
