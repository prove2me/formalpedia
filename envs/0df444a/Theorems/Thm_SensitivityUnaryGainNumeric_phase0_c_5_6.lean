-- Prove2me | Theorems.Thm_SensitivityUnaryGainNumeric_phase0_c_5_6
-- name    : SensitivityUnaryGainNumeric.phase0_c_5_6
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T16:00:22.989664+00:00
-- url     : https://prove2.me/theorems/5da3f81f-fe8e-4d57-a77b-56c8b167fe3b
-- title:
--   Unary prescribed gain certificate at ranks $(5,6)$
-- statement:
--   Fix ranks $(i,j)=(5,6)$ in the unary Paley recipe. Let $v$ be the input profile and let $C_w(i,j)$ be the prescribed-gain coordinate of the recorded first image. For every enumerated warm state $s$ that is rejected at rank $i$, the numerical own-target and guard-repair cutoffs are valid, and
--
--   $$\operatorname{Own}_v(s)+\sum_{h\in G(s)}\operatorname{Guard}_v(i,j,s,h)\le C_w(5,6).$$
--
--   Here $G(s)$ is the list of occupied guard heights, and the two fees are computed from the fixed profile and the recipe's repair cutoffs. Cutoff validity means that every legal own target reaches at least the state's current height, every possible guard repair has a strictly smaller cutoff than its old height, and height zero cannot be a possible guard repair. This is the finite prescribed-gain certificate used by the unary semantic transfer.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainChecks/C05_06.lean lines 4–7; SHA256 0c75e70b68b68882a766981e873e153c5ecfc367023ec371119b396e25452431; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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


open SensitivityUnaryGainNumeric

theorem SensitivityUnaryGainNumeric.phase0_c_5_6 :
    warmCheckFast phase0 SensitivityLiteralRay.rayData 5 6
      (SensitivityLocalNumeric.entry SensitivityLiteralRay.image0Data 3 5 6) = true := by sorry
