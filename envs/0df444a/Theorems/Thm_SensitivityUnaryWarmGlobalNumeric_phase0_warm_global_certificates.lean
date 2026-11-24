-- Prove2me | Theorems.Thm_SensitivityUnaryWarmGlobalNumeric_phase0_warm_global_certificates
-- name    : SensitivityUnaryWarmGlobalNumeric.phase0_warm_global_certificates
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T16:02:47.667149+00:00
-- url     : https://prove2.me/theorems/149ccd4a-a561-4202-907e-535f576813ea
-- title:
--   Phase-zero global-gain certificates at warm ranks
-- statement:
--   For every $0\le i\le j<12$ with $j\ge5$, the warm global-gain checker accepts the literal phase-zero prices and output $A$-entry:
--   $$
--   \operatorname{check}\!\left(r_0,\mathrm{ray},i,j,p_{0,i,j},
--   \mathrm{image}_{0,A}(i,j)\right)=\mathrm{true}.
--   $$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryWarmGlobalCertificates.lean lines 72–219; SHA256 5650fc418e55a81740f8f7bed9ad9164b3c331b6a60df42db7f529b60b11d725; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LiteralProfileData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryWarmGlobalData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryWarmGlobalNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Range
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace SensitivityUnaryWarmGlobalNumeric
end SensitivityUnaryWarmGlobalNumeric


set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open SensitivityUnaryWarmGlobalNumeric

theorem SensitivityUnaryWarmGlobalNumeric.phase0_warm_global_certificates (i j : Fin 12) (hij : i ≤ j) (hj : 5 ≤ j.val) :
    check SensitivityUnaryGainNumeric.phase0 SensitivityLiteralRay.rayData i j (phase0Prices i j)
      (SensitivityLocalNumeric.entry SensitivityLiteralRay.image0Data 0 i.val j.val) = true := by sorry
