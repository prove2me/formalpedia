-- Prove2me | Theorems.Thm_SensitivityUnaryGainNumeric_phase0_warm_c_certificates
-- name    : SensitivityUnaryGainNumeric.phase0_warm_c_certificates
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:50:39.897684+00:00
-- url     : https://prove2.me/theorems/e7d8cd88-9d60-4e85-a7a4-430c453d11ca
-- title:
--   Phase-zero prescribed-gain certificates at strict ranks
-- statement:
--   For every interval $0\le i\le j<12$ with $j\ge5$, the exact warm prescribed-gain checker verifies the literal phase-zero $C$-entry:
--   $$
--   \operatorname{warmCheckFast}
--   \bigl(r_0,\mathrm{ray},i,j,\mathrm{image}_{0,C}(i,j)\bigr)=\mathrm{true}.
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainCertificates.lean lines 237–384; SHA256 a49405a186d747f572d37fbbeeb5acd731c277c187d7880ff2e80eb3351d450b; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LiteralProfileData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainFast
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Range
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace SensitivityUnaryGainNumeric
end SensitivityUnaryGainNumeric


set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open SensitivityUnaryGainNumeric

theorem SensitivityUnaryGainNumeric.phase0_warm_c_certificates (i j : Fin 12) (hij : i ≤ j) (hj : 5 ≤ j.val) :
    warmCheckFast phase0 SensitivityLiteralRay.rayData i j
      (SensitivityLocalNumeric.entry SensitivityLiteralRay.image0Data 3 i.val j.val) = true := by sorry
