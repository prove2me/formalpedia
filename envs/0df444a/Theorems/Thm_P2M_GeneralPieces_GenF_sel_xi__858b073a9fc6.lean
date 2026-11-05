-- Prove2me | Theorems.Thm_P2M_GeneralPieces_GenF_sel_xi__858b073a9fc6
-- name    : P2M_GeneralPieces_GenF_sel_xi__858b073a9fc6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:41.506825+00:00
-- url     : https://prove2.me/theorems/81611dfb-37b5-4d48-b1ad-b53499eeacbd
-- title:
--   P2 M General Pieces Gen F sel xi  858b073a9fc6: P2 M General Pieces Gen F sel xi  858b073a9fc6
-- statement:
--   On the inner family, with the value 0 at the index 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L50-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L50-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
variable {R : Type} [Zero R]

theorem P2M_GeneralPieces_GenF_sel_xi__858b073a9fc6 (rd : Bool) (f g : ℕ → R) (n : ℕ) : sel rd f g (xi rd n) = z0 f n := by sorry

alias «GeneralPieces».«GenF».«sel_xi'» := P2M_GeneralPieces_GenF_sel_xi__858b073a9fc6
