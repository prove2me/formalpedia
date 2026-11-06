-- Prove2me | Theorems.Thm_RecursionToBound_countOutput_polyT
-- name    : RecursionToBound.countOutput_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:23:24.669197+00:00
-- url     : https://prove2.me/theorems/068df3ab-8828-4d8d-8491-813e2581be25
-- title:
--   Recursion To Bound: count Output poly T
-- statement:
--   The count of the output at a node is polynomial-time jointly in k, the padding string, the
--   index, n and the node, if k and n are given in unary; given the certificate of Steps 2 to 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L91-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L91-L100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Exponent
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_StepSparsify_CertWalk
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_RecursionToBound_Cert_Top
set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

theorem RecursionToBound.countOutput_polyT (hC : StCertCountD) (hP : S.Poly) {k n : α → ℕ} {pad : α → U} {i : α → Idx} {x : α → CNode} (hk : Unary k) (hp : PolyT pad) (hi : PolyT i) (hn : Unary n)
    (hx : PolyT x) : PolyT fun a => countOutput S (k a) (pad a) (i a) (n a) (x a) := by sorry
