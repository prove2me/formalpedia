-- Prove2me | Theorems.Thm_PolyClinch_TwoSided_proposition_3_8
-- name    : PolyClinch.TwoSided.proposition_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:51.031028+00:00
-- url     : https://prove2.me/theorems/598ffc15-fc34-41db-b388-e471d21cbb97
-- title:
--   Proposition 3.8, p. 13 — Mechanism 2 satisfies (IRs)
-- statement:
--   Let $\mathcal I$ be valid public information and $\varepsilon>0$. Every allocation output by Mechanism 2 gives each seller $j$ at least his initial utility:
--   $$
--   u_j(w,p,r)=r_j+\rho_j\bigl(f_j(E_j)-w(E_j)\bigr)\ \ge\ \rho_j f_j(E_j).
--   $$
--   Equivalently (by (4)), the revenue of seller $j$ is at least $\rho_j w(E_j)$: his goods are sold at price at least $\rho_j$.
--
--   **Formalization Note** "Output of Mechanism 2" is the relation `Mech2Outcome`; $w(E_j)$ is summed over the original edges of seller $j$, the virtual edge carrying his unsold goods.
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, p. 13, Proposition 3.8; proof in §5.1, p. 24

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Clinching

namespace PolyClinch.TwoSided

/-- Proposition 3.8 (Hirai–Sato p. 13). Mechanism 2 satisfies (IRs): every output `A` of
Mechanism 2 on a valid input gives each seller `j` utility at least `ρ_j f_j(E_j)`. -/
theorem proposition_3_8 {n m : ℕ} (E : Finset (Fin n × Fin m)) (ε : ℝ) (hε : 0 < ε)
    (I : PublicInfo E) (hI : Valid E ε I) (A : Allocation E) (hA : Mech2Outcome E I ε A) :
    ∀ j, I.rho j * I.f j (edgesOfSeller E j) ≤ sellerUtility E I A j := by sorry

end PolyClinch.TwoSided
