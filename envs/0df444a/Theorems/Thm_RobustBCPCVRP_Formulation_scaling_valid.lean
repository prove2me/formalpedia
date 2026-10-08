-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_scaling_valid
-- name    : RobustBCPCVRP.Formulation.scaling_valid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:41:55.983185+00:00
-- url     : https://prove2.me/theorems/a2ed2fdc-9a27-4957-b2be-417f8d01114e
-- title:
--   §3.1, p. 7 — q-routes for the scaled demands ⌈dᵥ/g⌉ and capacity ⌊C/g⌋ are valid q-routes
-- statement:
--   Let $G=(V,E)$ be a graph with integer demands $d_v\ge 0$ and integer capacity $C$, and let $g>1$ be an integer. Define the scaled demands and capacity
--   $$d'_v(g)=\lceil d_v/g\rceil,\qquad C'=\lfloor C/g\rfloor .$$
--   Every q-route without 2-cycles for the scaled data $(d',C')$ is a q-route without 2-cycles for the original data $(d,C)$; in particular its original load is at most $C$.
--
--   This is the correctness of the scaling acceleration of the pricing: the dynamic program run on the scaled instance takes time proportional to $C'$ instead of $C$, and the columns it finds remain valid.
--
--   **Formalization Note** $\lceil\cdot\rceil$ and $\lfloor\cdot\rfloor$ are taken over the rationals (`⌈(d v : ℚ) / g⌉₊`, `⌊(C : ℚ) / g⌋₊`).
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 7, §3.1, Heuristic Acceleration, scaling

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem scaling_valid {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (C g : ℕ) (hg : 1 < g) (r : List (Fin (n + 1)))
    (hr : IsQRoute E (fun v => ⌈(d v : ℚ) / g⌉₊) ⌊(C : ℚ) / g⌋₊ r) :
    IsQRoute E d C r := by sorry
end RobustBCPCVRP.Formulation
