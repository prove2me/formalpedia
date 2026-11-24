-- Prove2me | Theorems.Thm_SensitivityUnaryGainNumeric_phase0_c_5_7
-- name    : SensitivityUnaryGainNumeric.phase0_c_5_7
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T16:00:18.674827+00:00
-- url     : https://prove2.me/theorems/249b3b1d-af47-49dc-9e31-901ce5826294
-- title:
--   Unary prescribed gain certificate at ranks $(5,7)$
-- statement:
--   Fix ranks $(i,j)=(5,7)$ in the unary Paley recipe. Let $v$ be the input profile and let $C_w(i,j)$ be the prescribed-gain coordinate of the recorded first image. For every enumerated warm state $s$ that is rejected at rank $i$, the numerical own-target and guard-repair cutoffs are valid, and
--
--   $$\operatorname{Own}_v(s)+\sum_{h\in G(s)}\operatorname{Guard}_v(i,j,s,h)\le C_w(5,7).$$
--
--   Here $G(s)$ is the list of occupied guard heights, and the two fees are computed from the fixed profile and the recipe's repair cutoffs. Cutoff validity means that every legal own target reaches at least the state's current height, every possible guard repair has a strictly smaller cutoff than its old height, and height zero cannot be a possible guard repair. This is the finite prescribed-gain certificate used by the unary semantic transfer.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainChecks/C05_07.lean lines 8–10; SHA256 cb276f13e7f66f7b7db21d4f8ed629e5060bb52e1db30320577b61fc8c32dc1a; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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


/-! Exact unary C(5,7) certificate.  Closed arithmetic is checked by the kernel. -/
open SensitivityUnaryGainNumeric
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem SensitivityUnaryGainNumeric.phase0_c_5_7 :
    warmCheckFast phase0 SensitivityLiteralRay.rayData 5 7
      (SensitivityLocalNumeric.entry SensitivityLiteralRay.image0Data 3 5 7) = true := by sorry
