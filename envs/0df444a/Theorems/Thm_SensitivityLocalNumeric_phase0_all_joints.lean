-- Prove2me | Theorems.Thm_SensitivityLocalNumeric_phase0_all_joints
-- name    : SensitivityLocalNumeric.phase0_all_joints
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:50:40.723932+00:00
-- url     : https://prove2.me/theorems/a28be9f4-5d50-409e-8314-6e7874b07218
-- title:
--   All phase-zero joint-event triples are certified
-- statement:
--   For every triple of ranks satisfying $5\le w\le a<n<12$, the phase-zero recurrence has a verified joint certificate using the literal first output profile:
--   $$
--   \operatorname{JointCertified}
--   (r_0,v_0,\mathrm{image}_0,w,a,n,p_0(a,n),j_0(w,a,n)).
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/LocalNumericPhase0.lean lines 129–565; SHA256 b50c463853f3b0e6aa141fa3654be1377b8887feeeedf1116e948116d628856f; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LiteralProfileData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericCertificatesCore
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Range
import Mathlib.Tactic.FinCases

namespace SensitivityLocalNumeric
end SensitivityLocalNumeric


open SensitivityLocalNumeric
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem SensitivityLocalNumeric.phase0_all_joints : ∀ c x n : Fin 12, 5 ≤ c.val → c ≤ x → x < n →
    JointCertified phase0 input0 SensitivityLiteralRay.image0Data
      c x n (p0 x.val n.val) (j0 c.val x.val n.val) := by sorry
