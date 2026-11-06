-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_selectedIncidenceCount_eq_sum_neighborhood
-- name    : QEC.Coding.FiberBundle.RandomBase.selectedIncidenceCount_eq_sum_neighborhood
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T05:45:27.250521+00:00
-- url     : https://prove2.me/theorems/b2555e4a-4216-48a3-ad5e-615106338cc5
-- title:
--   Random Base: selected Incidence Count eq sum neighborhood
-- statement:
--   Variables outside the neighborhood contribute zero selected incidences.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L161-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Expansion.lean#L161-L174

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators

theorem QEC.Coding.FiberBundle.RandomBase.selectedIncidenceCount_eq_sum_neighborhood
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    selectedIncidenceCount sample S =
      ∑ b ∈ checkSetNeighborhood sample S,
        selectedCheckCount sample S b := by sorry
