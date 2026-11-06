-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_cMax_nonneg
-- name    : QEC.Locality.BKQLDPCFamily.cMax_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:59:03.885949+00:00
-- url     : https://prove2.me/theorems/17fd863a-447d-4064-9ed0-fc53b27678f8
-- title:
--   BKQLDPCFamily: c Max nonneg
-- statement:
--   The finite maximum inherits the proved exponent domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L354-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L354-L358

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]

theorem QEC.Locality.BKQLDPCFamily.cMax_nonneg (family : BKQLDPCFamily ι κ) (i : family.Index) :
    0 ≤ family.cMax i := by sorry
