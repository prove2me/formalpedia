-- Prove2me | Theorems.Thm_SystemSqueeze_Accommodation_no_entry_equilibrium
-- name    : SystemSqueeze.Accommodation.no_entry_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:15.499491+00:00
-- url     : https://prove2.me/theorems/9600bff1-3751-481a-b883-e79937c2fbfc
-- title:
--   §4.2 A, p. 11 — the no-entry price equilibrium is P_{C_i} = U_C/3 with profit U_C²/9
-- statement:
--   Let $U_C>0$. In the no-entry subgame each complementor $i\in\{A,B\}$ earns $P_{C_i}(U_C-P_{C_A}-P_{C_B})$. A price pair is a Nash equilibrium of this subgame if and only if
--   $$P_{C_A}=P_{C_B}=\frac{U_C}{3},$$
--   and at the equilibrium each firm earns $U_C^2/9$.
--
--   This is the benchmark against which the entry incentives of stage 1 are measured.
-- source:
--   Reisinger, Schmidt & Stieglitz, How Complementors Benefit from Taking Competition to the System Level, authors' manuscript (May 2020; Management Science, doi:10.1287/mnsc.2020.3771), p. 11 (PDF 12), §4.2 A

import Mathlib
import Definitions.Def_SystemSqueeze_Accommodation_Model

namespace SystemSqueeze.Accommodation

/-- §4.2 A, p. 11: in the no-entry subgame the unique price equilibrium is
`P_{C_A} = P_{C_B} = UC/3`, and each firm earns `UC²/9`. -/
theorem no_entry_equilibrium (UC : ℝ) (hUC : 0 < UC) (p : NoEntryPrices) :
    (IsNoEntryEq UC p ↔ p.pCA = UC / 3 ∧ p.pCB = UC / 3) ∧
    (IsNoEntryEq UC p → profitA0 UC p = UC ^ 2 / 9 ∧ profitB0 UC p = UC ^ 2 / 9) := by sorry

end SystemSqueeze.Accommodation
