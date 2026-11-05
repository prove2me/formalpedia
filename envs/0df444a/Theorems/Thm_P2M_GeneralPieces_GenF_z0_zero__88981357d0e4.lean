-- Prove2me | Theorems.Thm_P2M_GeneralPieces_GenF_z0_zero__88981357d0e4
-- name    : P2M_GeneralPieces_GenF_z0_zero__88981357d0e4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:32.069606+00:00
-- url     : https://prove2.me/theorems/3f7e454a-9c9b-438b-abc4-34e254c00e6e
-- title:
--   P2 M General Pieces Gen F z0 zero  88981357d0e4: P2 M General Pieces Gen F z0 zero  88981357d0e4
-- statement:
--   The P2 M General Pieces Gen F z0 zero  88981357d0e4 construction uses the P2 M General Pieces Gen F z0 zero  88981357d0e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L108-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean#L108-L110

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
import Definitions.Def_GeneralPieces_GenF_Kappa
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset

theorem P2M_GeneralPieces_GenF_z0_zero__88981357d0e4 {R : Type} [Zero R] (n : ℕ) : z0 (0 : ℕ → R) n = 0 := by sorry

alias «GeneralPieces».«GenF».«z0_zero'» := P2M_GeneralPieces_GenF_z0_zero__88981357d0e4
