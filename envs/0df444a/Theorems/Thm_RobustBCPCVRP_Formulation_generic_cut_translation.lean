-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_generic_cut_translation
-- name    : RobustBCPCVRP.Formulation.generic_cut_translation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:00.26542+00:00
-- url     : https://prove2.me/theorems/2e04aa74-0c5b-426c-b5dd-dfc325b090f3
-- title:
--   §2, p. 5 — a generic cut Σ aₑxₑ ≥ b becomes Σⱼ (Σₑ aₑqⱼᵉ) λⱼ ≥ b
-- statement:
--   Let $G=(V,E)$ be a graph, let $\lambda$ be finitely supported weights on client lists (columns $j$ with edge incidences $q^e_j$), and let $x$ satisfy (5), $x_e=\sum_j q^e_j\lambda_j$ for all $e\in E$. Then for every coefficient vector $a$ and every $b\in\mathbb R$,
--   $$\sum_{e\in E}a_e x_e\ge b\iff\sum_j\Big(\sum_{e\in E}a_e q^e_j\Big)\lambda_j\ge b .$$
--
--   Any valid inequality on the edge variables can therefore be added to the Dantzig–Wolfe Master without changing the structure of the pricing problem; this is what makes the method "robust".
--
--   **Formalization Note** The statement needs neither nonnegativity of $\lambda$ nor that its support consists of q-routes; it holds for any weights satisfying (5).
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 5, §2, last paragraph

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem generic_cut_translation {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (x : Sym2 (Fin (n + 1)) → ℝ) (lam : List (Fin (n + 1)) →₀ ℝ)
    (h5 : ∀ e ∈ E, colSum lam e = x e) (a : Sym2 (Fin (n + 1)) → ℝ) (b : ℝ) :
    b ≤ ∑ e ∈ E, a e * x e ↔
      b ≤ ∑ r ∈ lam.support, (∑ e ∈ E, a e * (inc r e : ℝ)) * lam r := by sorry
end RobustBCPCVRP.Formulation
