-- Prove2me | Theorems.Thm_PolyhedralSOC_Sandwich_feas_subset_feasRelaxed
-- name    : PolyhedralSOC.Sandwich.feas_subset_feasRelaxed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:52:24.382209+00:00
-- url     : https://prove2.me/theorems/42c2baf1-c4a5-42ba-a47d-925be2a36ea4
-- title:
--   Right inclusion in (14): Feas(CQP) ⊆ Feas(CQP_ε)
-- statement:
--   Let (CQP) be a conic quadratic problem and let $\varepsilon>0$. Every feasible point of (CQP) is feasible for its $\varepsilon$-relaxation (CQP$_\varepsilon$):
--   $$
--   \mathrm{Feas}(\mathrm{CQP})\subseteq\mathrm{Feas}(\mathrm{CQP}_\varepsilon).
--   $$
--
--   This is the right inclusion in (14) of Proposition 4.1, which the paper takes as already known from the definition of the relaxation (p. 194).
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 194 (PDF 2), sentence introducing (CQP_ε); p. 203 (PDF 11), Proposition 4.1, (14) right inclusion and first sentence of the proof

import Mathlib
import Definitions.Def_PolyhedralSOC_Sandwich_CQP

namespace PolyhedralSOC.Sandwich

/-- The right inclusion in (14): `Feas(CQP) ⊂ Feas(CQP_ε)` for `ε > 0`
(Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), p. 194 (PDF p. 2): the feasible set of (LP) is
"in between the feasible set of (CQP) and that of its ε-relaxation"; p. 203 (PDF p. 11),
proof of Proposition 4.1: "We already know that the right inclusion in (14) holds true"). -/
theorem feas_subset_feasRelaxed {n k₀ m : ℕ} (P : CQP n k₀ m) (ε : ℝ) (hε : 0 < ε) :
    feas P ⊆ feasRelaxed P ε := by sorry

end PolyhedralSOC.Sandwich
