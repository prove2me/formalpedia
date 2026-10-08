-- Prove2me | Theorems.Thm_RobustBCPCVRP_Formulation_dwm_substitution
-- name    : RobustBCPCVRP.Formulation.dwm_substitution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:41:56.576157+00:00
-- url     : https://prove2.me/theorems/0b05821e-b77b-4877-b88f-4baa022899fa
-- title:
--   §2, p. 5 — the DWM (8)–(11) is (1)–(4) with x replaced by Qλ through (5)
-- statement:
--   Let $\lambda\ge 0$ be weights on q-routes without 2-cycles in a CVRP instance with graph $G=(V,E)$, demands $d$, $K$ vehicles, capacity $C$ and lengths $\ell$, and put $x=Q\lambda$, i.e. $x_e=\sum_j q^e_j\lambda_j$. Then
--
--   1. $\lambda$ satisfies the DWM constraints (8)–(11) if and only if $x$ satisfies (1)–(4);
--   2. $x$ vanishes off $E$ and $x\ge 0$;
--   3. the DWM objective equals the edge objective:
--   $$\sum_j\sum_{e\in E}\ell_e q^e_j\lambda_j=\sum_{e\in E}\ell_e x_e .$$
--
--   This is the paper's passage from the Explicit Master to the more compact Dantzig–Wolfe Master: every occurrence of $x_e$ in (1)–(4) is replaced by its value given by (5).
--
--   **Formalization Note** In (8)–(10) the DWM is written with the paper's double sums $\sum_j\sum_{e\in\delta(\cdot)}q^e_j\lambda_j$, whereas (1)–(3) are written on the cut value of $x=Q\lambda$; part 1 is the exchange of these sums.
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 5, §2, DWM (7)–(11)

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
open LysgaardCVRP.Shrink

namespace RobustBCPCVRP.Formulation
theorem dwm_substitution {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (K C : ℕ) (ℓ : Sym2 (Fin (n + 1)) → ℝ)
    (lam : List (Fin (n + 1)) →₀ ℝ) (hlam : IsColumns E d C lam) :
    (IsDWMFeasible E d K C lam ↔
      Deg1 (colSum lam) ∧ Deg2 K (colSum lam) ∧ Cap3 d C (colSum lam) ∧ Bnd4 E (colSum lam)) ∧
    OnE E (colSum lam) ∧ Nonneg (colSum lam) ∧
    dwmObjective E ℓ lam = ∑ e ∈ E, ℓ e * colSum lam e := by sorry
end RobustBCPCVRP.Formulation
