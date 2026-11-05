-- Prove2me | Theorems.Thm_VariableBound_Net_CertRank_choose_min
-- name    : VariableBound.Net.CertRank.choose_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:33.524069+00:00
-- url     : https://prove2.me/theorems/447fb15e-97c3-4ecc-92c5-0d0e0196f7b8
-- title:
--   Cert Rank: choose min
-- statement:
--   C(t, μ) does not change if μ is cut off at t + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertRank.lean#L69-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertRank.lean#L69-L72

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

theorem VariableBound.Net.CertRank.choose_min (t μ : ℕ) : t.choose (min μ (t + 1)) = t.choose μ := by sorry
