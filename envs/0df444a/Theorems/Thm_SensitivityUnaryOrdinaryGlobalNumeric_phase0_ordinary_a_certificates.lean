-- Prove2me | Theorems.Thm_SensitivityUnaryOrdinaryGlobalNumeric_phase0_ordinary_a_certificates
-- name    : SensitivityUnaryOrdinaryGlobalNumeric.phase0_ordinary_a_certificates
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T16:02:51.525801+00:00
-- url     : https://prove2.me/theorems/3065a0b3-73ad-4334-bce2-7d38bce64143
-- title:
--   Phase-zero global-gain certificates at ordinary ranks
-- statement:
--   For every $0\le i\le j<5$, the ordinary global-gain checker accepts the literal phase-zero $A$-entry, using the phase-zero allowance and prices:
--   $$
--   \operatorname{check}\!\left(q_j,\,[i=j],\,p_0,\,
--   \mathrm{image}_{0,A}(i,j)\right)=\mathrm{true}.
--   $$
--   The Boolean parameter allows guard-head cases precisely for diagonal intervals.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryOrdinaryGlobalCertificates.lean lines 21–168; SHA256 359ec0ccfb06ab222f3c55ff1fe45eb24e893273d2e4e5d364ad34dbf06eaf18; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LiteralProfileData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FinCases

namespace SensitivityUnaryOrdinaryGlobalNumeric
end SensitivityUnaryOrdinaryGlobalNumeric


open SensitivityUnaryOrdinaryGlobalNumeric

theorem SensitivityUnaryOrdinaryGlobalNumeric.phase0_ordinary_a_certificates (i j : Fin 12) (hij : i ≤ j) (hj : j.val < 5) :
    check (SensitivityUnaryGainNumeric.phase0.allowance j) (decide (i = j)) phase0Prices
      (SensitivityLocalNumeric.entry SensitivityLiteralRay.image0Data 0 i.val j.val) = true := by sorry
