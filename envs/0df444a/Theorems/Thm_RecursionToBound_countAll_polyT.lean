-- Prove2me | Theorems.Thm_RecursionToBound_countAll_polyT
-- name    : RecursionToBound.countAll_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:23:46.283803+00:00
-- url     : https://prove2.me/theorems/92253aac-604e-4687-b3d8-498955886c1d
-- title:
--   Recursion To Bound: count All poly T
-- statement:
--   The sum of the counts of all outputs is polynomial-time jointly in k, r, the index, the decoded
--   formula and the padding string, if k and 2^k are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L104-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L104-L111

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
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d

set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

theorem RecursionToBound.countAll_polyT (hC : StCertCountD) (hP : S.Poly) {k : α → ℕ} {r : α → ℕ × ℕ} {i : α → Idx} {d : α → U × Fml} {pad : α → U} (hk : Unary k) (h2 : Unary fun a => 2 ^ k a)
    (hr : PolyT r) (hi : PolyT i) (hd : PolyT d) (hp : PolyT pad) : PolyT fun a => countAll S (k a) (r a) (i a) (d a) (pad a) := by sorry
