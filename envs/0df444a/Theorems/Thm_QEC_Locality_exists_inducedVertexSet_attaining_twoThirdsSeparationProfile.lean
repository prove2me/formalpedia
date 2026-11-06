-- Prove2me | Theorems.Thm_QEC_Locality_exists_inducedVertexSet_attaining_twoThirdsSeparationProfile
-- name    : QEC.Locality.exists_inducedVertexSet_attaining_twoThirdsSeparationProfile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:08:05.902108+00:00
-- url     : https://prove2.me/theorems/45374ed1-12b9-4e7a-852e-247c626f6301
-- title:
--   Locality: exists induced Vertex Set attaining two Thirds Separation Profile
-- statement:
--   The measured profile maximum is attained by an explicit induced vertex set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L138-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L138-L150

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
set_option autoImplicit false
open QEC QEC.Locality
universe u

theorem QEC.Locality.exists_inducedVertexSet_attaining_twoThirdsSeparationProfile
    {ι : Type u} [Fintype ι] [DecidableEq ι] (G : ConnectivityGraph ι) (scale : Nat) :
    ∃ vertices : Finset ι,
      vertices ⊆ Finset.univ ∧ vertices.card ≤ scale ∧
        minimumTwoThirdsBalancedVertexSeparatorSize G vertices =
          twoThirdsSeparationProfile G scale := by sorry
