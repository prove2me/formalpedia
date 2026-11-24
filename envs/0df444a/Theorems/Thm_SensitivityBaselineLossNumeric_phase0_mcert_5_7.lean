-- Prove2me | Theorems.Thm_SensitivityBaselineLossNumeric_phase0_mcert_5_7
-- name    : SensitivityBaselineLossNumeric.phase0_mcert_5_7
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:48:42.686868+00:00
-- url     : https://prove2.me/theorems/0a22d860-e911-4214-bf66-afb314cdd2f2
-- title:
--   Unary baseline loss certificate at ranks $(5,7)$
-- statement:
--   Fix ranks $(i,j)=(5,7)$ in the twelve-rank unary Paley recipe $r_0$. Let $v$ be the checkpoint input profile, $w$ its first recorded image, and $D_{i,j}$ the stored table of integer dual certificates. A state $s=(a,b,f_i,f_j)$ is admissible when its heights, failure counts, and both acceptance tests satisfy the recipe's finite state conditions; the branch $b_0\in\{0,1\}$ obeys the prescribed top-rank restriction. Then
--
--   $$\forall(s,b_0)\in\mathcal{A}_{5,7},\quad V_{5,7}\bigl(s,b_0;D_{5,7}(\operatorname{key}(s,b_0))\bigr).$$
--
--   Here $V_{i,j}$ is dual validity: the denominator is positive, the extra-demand coefficient is nonpositive, every allowed guard column has a valid height cutoff and is dominated by the dual weights, and the resulting total weighted cost is at most the output loss bound $M_w(i,j)$. This supplies the numerical certificate required by the generic baseline-loss bound at these two ranks.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M05_07.lean lines 56–57; SHA256 f730969064931571cce100f8d5d992ebe41c0da245597477e78aa7d6588e5f63; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M05_07
import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

namespace SensitivityBaselineLossNumeric
end SensitivityBaselineLossNumeric


open SensitivityBaselineLossNumeric
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false

theorem SensitivityBaselineLossNumeric.phase0_mcert_5_7 : Certified phase0 input0 output0 5 7 phase0_mdual_5_7 := by sorry
