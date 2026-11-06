-- Prove2me | Theorems.Thm_QEC_Locality_minimumSeparator_card_le_ownProfile
-- name    : QEC.Locality.minimumSeparator_card_le_ownProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:27.259043+00:00
-- url     : https://prove2.me/theorems/c3bc9f52-0bdd-4d14-bb8a-c92ece33b420
-- title:
--   Locality: minimum Separator card le own Profile
-- statement:
--   An exact minimum separator is bounded by the measured profile at its own scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L271-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L271-L278

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.minimumSeparator_card_le_ownProfile
    (G : ConnectivityGraph ι) (vertices separator : Finset ι)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices) :
    separator.card ≤ twoThirdsSeparationProfile G vertices.card := by sorry
