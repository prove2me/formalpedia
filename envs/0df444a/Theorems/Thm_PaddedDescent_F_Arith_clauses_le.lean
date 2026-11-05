-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_clauses_le
-- name    : PaddedDescent.F.Arith.clauses_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:12.430671+00:00
-- url     : https://prove2.me/theorems/da5a18bc-0b2f-42f9-8d66-bec8c6faf1e0
-- title:
--   Arith: clauses le
-- statement:
--   Field m_le of MarkFits: the number of clauses is at most 2^β·(n + 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L420-L421
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L420-L421

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F

theorem PaddedDescent.F.Arith.clauses_le {Δ s : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (n : ℕ) : Δ * n ≤ 2 ^ betaOf s * (n + 1) := by sorry
