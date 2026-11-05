-- Prove2me | Theorems.Thm_VariableBound_Net_CertRank_foldr_stepR
-- name    : VariableBound.Net.CertRank.foldr_stepR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:43:51.870845+00:00
-- url     : https://prove2.me/theorems/c699e7f6-1811-4f4d-82da-6cde8fd59a83
-- title:
--   Cert Rank: foldr step R
-- statement:
--   The fold yields the string and its position.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertRank.lean#L33-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertRank.lean#L33-L36

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

theorem VariableBound.Net.CertRank.foldr_stepR (x : List Bool) : x.foldr stepR ([], 0) = (x, rank x) := by sorry
