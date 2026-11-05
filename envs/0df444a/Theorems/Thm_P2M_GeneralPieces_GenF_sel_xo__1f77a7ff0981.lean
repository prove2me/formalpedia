-- Prove2me | Theorems.Thm_P2M_GeneralPieces_GenF_sel_xo__1f77a7ff0981
-- name    : P2M_GeneralPieces_GenF_sel_xo__1f77a7ff0981
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:32:03.980561+00:00
-- url     : https://prove2.me/theorems/947ec72c-e8a4-49e1-9ec6-878205141c76
-- title:
--   P2 M General Pieces Gen F sel xo  1f77a7ff0981: P2 M General Pieces Gen F sel xo  1f77a7ff0981
-- statement:
--   On the outer family, with the value 0 at the index 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L54-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L54-L55

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

theorem P2M_GeneralPieces_GenF_sel_xo__1f77a7ff0981 (rd : Bool) (f g : ℕ → R) (n : ℕ) : sel rd f g (xo rd n) = z0 g n := by sorry

alias «GeneralPieces».«GenF».«sel_xo'» := P2M_GeneralPieces_GenF_sel_xo__1f77a7ff0981
