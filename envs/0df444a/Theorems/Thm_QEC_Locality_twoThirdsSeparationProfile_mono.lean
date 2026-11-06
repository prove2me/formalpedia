-- Prove2me | Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_mono
-- name    : QEC.Locality.twoThirdsSeparationProfile_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:10:34.983614+00:00
-- url     : https://prove2.me/theorems/db951246-9087-47c2-aae0-c66dd0645767
-- title:
--   Locality: two Thirds Separation Profile mono
-- statement:
--   The measured profile is monotone in its induced-subgraph cardinality bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L164-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L164-L174

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
set_option autoImplicit false
open QEC QEC.Locality
universe u

theorem QEC.Locality.twoThirdsSeparationProfile_mono {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) {small large : Nat} (hscale : small ≤ large) :
    twoThirdsSeparationProfile G small ≤ twoThirdsSeparationProfile G large := by sorry
