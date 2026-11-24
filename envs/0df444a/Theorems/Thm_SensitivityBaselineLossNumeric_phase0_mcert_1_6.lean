-- Prove2me | Theorems.Thm_SensitivityBaselineLossNumeric_phase0_mcert_1_6
-- name    : SensitivityBaselineLossNumeric.phase0_mcert_1_6
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:45:26.43633+00:00
-- url     : https://prove2.me/theorems/6be1f755-5aaa-4145-b5fd-ce14504c1ba0
-- title:
--   Unary baseline loss certificate at ranks $(1,6)$
-- statement:
--   Fix ranks $(i,j)=(1,6)$ in the twelve-rank unary Paley recipe $r_0$. Let $v$ be the checkpoint input profile, $w$ its first recorded image, and $D_{i,j}$ the stored table of integer dual certificates. A state $s=(a,b,f_i,f_j)$ is admissible when its heights, failure counts, and both acceptance tests satisfy the recipe's finite state conditions; the branch $b_0\in\{0,1\}$ obeys the prescribed top-rank restriction. Then
--
--   $$\forall(s,b_0)\in\mathcal{A}_{1,6},\quad V_{1,6}\bigl(s,b_0;D_{1,6}(\operatorname{key}(s,b_0))\bigr).$$
--
--   Here $V_{i,j}$ is dual validity: the denominator is positive, the extra-demand coefficient is nonpositive, every allowed guard column has a valid height cutoff and is dominated by the dual weights, and the resulting total weighted cost is at most the output loss bound $M_w(i,j)$. This supplies the numerical certificate required by the generic baseline-loss bound at these two ranks.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M01_06.lean lines 86–87; SHA256 d7b1c0170b2ab1a6a4c6b68fcb7e050b8af03c1d99792eda2b620233371661f2; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M01_06
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

theorem SensitivityBaselineLossNumeric.phase0_mcert_1_6 : Certified phase0 input0 output0 1 6 phase0_mdual_1_6 := by sorry
