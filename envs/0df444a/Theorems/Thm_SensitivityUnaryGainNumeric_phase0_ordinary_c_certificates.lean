-- Prove2me | Theorems.Thm_SensitivityUnaryGainNumeric_phase0_ordinary_c_certificates
-- name    : SensitivityUnaryGainNumeric.phase0_ordinary_c_certificates
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:50:40.251005+00:00
-- url     : https://prove2.me/theorems/f3ae9199-68d7-42f1-8ae9-800276979d39
-- title:
--   Phase-zero prescribed-gain certificates at ordinary ranks
-- statement:
--   For every interval $0\le i\le j<5$, the ordinary unary prescribed-gain checker accepts the literal phase-zero output entry:
--   $$
--   \operatorname{ordinaryCheck}
--   \bigl(\mathrm{ray},i,j,\mathrm{image}_{0,C}(i,j)\bigr).
--   $$
--   The entry is the $C$-coordinate of the first output profile.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGainCertificates.lean lines 88–235; SHA256 a49405a186d747f572d37fbbeeb5acd731c277c187d7880ff2e80eb3351d450b; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LiteralProfileData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
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

theorem SensitivityUnaryGainNumeric.phase0_ordinary_c_certificates (i j : Fin 12) (hij : i ≤ j) (hj : j.val < 5) :
    ordinaryCheck SensitivityLiteralRay.rayData i j
      (SensitivityLocalNumeric.entry SensitivityLiteralRay.image0Data 3 i.val j.val) := by sorry
