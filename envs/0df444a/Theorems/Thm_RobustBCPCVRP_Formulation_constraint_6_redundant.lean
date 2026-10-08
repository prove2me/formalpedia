-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_constraint_6_redundant
-- name    : RobustBCPCVRP.Formulation.constraint_6_redundant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:14.400021+00:00
-- url     : https://prove2.me/theorems/5f906fe3-4fea-4373-9a10-945a54381c9b
-- title:
--   §2, p. 5 — constraint (6) is implied by (2) and (5)
-- statement:
--   Let $\lambda\ge 0$ be weights on q-routes without 2-cycles in a CVRP instance with graph $G=(V,E)$, and let $x\in\mathbb R^E$ satisfy (5), $\sum_j q^e_j\lambda_j=x_e$ for all $e\in E$, and (2), $x(\delta(\{0\}))=2K$. Then (6) holds:
--   $$\sum_j\lambda_j=K .$$
--
--   This is why the Dantzig–Wolfe Master can drop the convexity-type row (6): every q-route leaves and re-enters the depot exactly once, so (2) already fixes the number of vehicles.
--
--   **Formalization Note** The vector $x$ is required to vanish off $E$ (the paper's $x\in\mathbb R^{|E|}$); otherwise $x(\delta(\{0\}))$ could count phantom non-edges.
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 5, §2, after the display of P₃

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem constraint_6_redundant {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (K C : ℕ) (x : Sym2 (Fin (n + 1)) → ℝ)
    (lam : List (Fin (n + 1)) →₀ ℝ) (hlam : IsColumns E d C lam)
    (h5 : ∀ e ∈ E, colSum lam e = x e) (hxE : OnE E x) (h2 : Deg2 K x) :
    colCount lam = (K : ℝ) := by sorry
end RobustBCPCVRP.Formulation
