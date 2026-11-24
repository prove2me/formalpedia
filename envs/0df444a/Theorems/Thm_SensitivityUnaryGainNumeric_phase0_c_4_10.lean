-- Prove2me | Theorems.Thm_SensitivityUnaryGainNumeric_phase0_c_4_10
-- name    : SensitivityUnaryGainNumeric.phase0_c_4_10
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T16:00:14.757194+00:00
-- url     : https://prove2.me/theorems/726fd9b8-206b-4cb0-bd04-3e63be23da78
-- title:
--   Unary prescribed gain certificate at ranks $(4,10)$
-- statement:
--   Fix ranks $(i,j)=(4,10)$ in the unary Paley recipe. Let $v$ be the input profile and let $C_w(i,j)$ be the prescribed-gain coordinate of the recorded first image. For every enumerated warm state $s$ that is rejected at rank $i$, the numerical own-target and guard-repair cutoffs are valid, and
--
--   $$\operatorname{Own}_v(s)+\sum_{h\in G(s)}\operatorname{Guard}_v(i,j,s,h)\le C_w(4,10).$$
--
--   Here $G(s)$ is the list of occupied guard heights, and the two fees are computed from the fixed profile and the recipe's repair cutoffs. Cutoff validity means that every legal own target reaches at least the state's current height, every possible guard repair has a strictly smaller cutoff than its old height, and height zero cannot be a possible guard repair. This is the finite prescribed-gain certificate used by the unary semantic transfer.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainChecks/C04_10.lean lines 8–10; SHA256 6ebc83a7376b7919a32f518843da7eb0a548c67b93cacc18343ec736465bbaa9; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LiteralProfileData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainFast
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Range

namespace SensitivityUnaryGainNumeric
end SensitivityUnaryGainNumeric


/-! Exact unary C(4,10) certificate.  Closed arithmetic is checked by the kernel. -/
open SensitivityUnaryGainNumeric
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem SensitivityUnaryGainNumeric.phase0_c_4_10 :
    warmCheckFast phase0 SensitivityLiteralRay.rayData 4 10
      (SensitivityLocalNumeric.entry SensitivityLiteralRay.image0Data 3 4 10) = true := by sorry
