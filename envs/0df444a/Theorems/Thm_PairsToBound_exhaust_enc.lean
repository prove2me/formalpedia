-- Prove2me | Theorems.Thm_PairsToBound_exhaust_enc
-- name    : PairsToBound.exhaust_enc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:24.321705+00:00
-- url     : https://prove2.me/theorems/b1c0b96d-80c9-4afd-9a92-c2c4b9d3cb75
-- title:
--   Pairs To Bound: exhaust enc
-- statement:
--   On the code of (k, φ), for k ≥ 1 and a k-CNF φ on n variables, with a padding string of 2ⁿ
--   units, exhaustive counting returns the number of satisfying assignments of φ in n + 1 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L78-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Exhaust.lean#L78-L84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Exhaust
set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg Wrap MainTheoremForms
open Sat3 (CNF)

theorem PairsToBound.exhaust_enc {k n : ℕ} (φ : CNF n) (hk : 1 ≤ k) (hφ : SatK.IsKCNF k φ) : exhaust (SatM.enc k φ, pad n) = SatK.binary n (SatK.numSat φ) := by sorry
