-- Prove2me | Theorems.Thm_VariableBound_Net_CertRank_len_rank_le
-- name    : VariableBound.Net.CertRank.len_rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:06.095421+00:00
-- url     : https://prove2.me/theorems/bd21c4d4-f603-40e4-beeb-26437c5e14f7
-- title:
--   Cert Rank: len rank le
-- statement:
--   The word of the position of a string is at most as long as the word of the string.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertRank.lean#L48-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertRank.lean#L48-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Rank
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertRank
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
open VariableBound.Net.CertRank

theorem VariableBound.Net.CertRank.len_rank_le (x : List Bool) : len (rank x) ≤ len x := by sorry
