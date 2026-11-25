-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_cauchyBinet
-- name    : ReciprocityTheory.ChartRestriction.DS.cauchyBinet
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:49:05.610804+00:00
-- url     : https://prove2.me/theorems/702b04e3-5cff-4078-bf1e-5fe615149c6f
-- title:
--   DS: cauchy Binet
-- statement:
--   The DS construction uses the cauchy Binet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CauchyBinet.lean#L62-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CauchyBinet.lean#L62-L108

import Mathlib
import Definitions.Def_Lemmata_GeneralBFact_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CauchyBinet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix MeasureTheory
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.cauchyBinet {m i : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin i) (Fin m) R)
    (B : Matrix (Fin m) (Fin i) R) :
    (A * B).det = ∑ S : {S : Finset (Fin m) // S.card = i},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by sorry
