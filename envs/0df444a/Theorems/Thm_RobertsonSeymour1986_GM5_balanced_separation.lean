-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_balanced_separation
-- name    : RobertsonSeymour1986.GM5.balanced_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:03:54.478788+00:00
-- url     : https://prove2.me/theorems/b8c1d5fa-9707-4562-ba5b-aaac3add5d88
-- title:
--   (7.1) Balanced separation of order at most $\theta_7$
-- statement:
--   Let $\theta\ge 6$ be even and let $G$ be a finite graph with no $\theta$-grid minor. Then $G$ has a separation $(V_1,V_2)$ such that
--
--   $$|V_1\cap V_2|\le\theta_7\quad\text{and}\quad |V_1-V_2|,\ |V_2-V_1|\le (1-\theta_8^{-1})\,|V(G)|,$$
--
--   where $\theta_7=\alpha(\theta_5,\theta_6)$ and $\theta_8=3\theta_5(3^{\theta_5}-1)/4$ are the parameters of Section 2.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (7.1), p. 106 (PDF p. 15); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor
import Definitions.Def_RobertsonSeymour1986_GM5_Params
import Definitions.Def_RobertsonSeymour1986_GM5_IsSeparation

namespace RobertsonSeymour1986.GM5

/-- (7.1): a graph without a θ-grid minor has a separation of order at most `θ₇` with both sides
of size at most `(1 − θ₈^{−1})|V(G)|`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (7.1), p. 106 (PDF p. 15): "If G ∈ 𝓕_θ then G has a separation (V₁, V₂) such that
|V₁ ∩ V₂| ≤ θ₇ and |V₁ − V₂|, |V₂ − V₁| ≤ (1 − θ₈^{−1})|V(G)|, where θ₇, θ₈ are as defined in
Section 2."

**Formalization Note** The standing assumption of p. 95 (PDF p. 4), "θ is a fixed even integer with θ ≥ 6", is the pair
of hypotheses `Even θ`, `6 ≤ θ`; "G ∈ 𝓕_θ" is `NoGridMinor θ G`. The bound `(1 − θ₈^{−1})|V(G)|` is compared in `ℚ`. -/
theorem balanced_separation {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (θ : ℕ) (hθe : Even θ) (hθ6 : 6 ≤ θ) (hG : NoGridMinor θ G) :
    ∃ V₁ V₂ : Finset V, IsSeparation G V₁ V₂ ∧ (V₁ ∩ V₂).card ≤ theta7 θ ∧
      ((V₁ \ V₂).card : ℚ) ≤ (1 - (theta8 θ : ℚ)⁻¹) * (Fintype.card V : ℚ) ∧
      ((V₂ \ V₁).card : ℚ) ≤ (1 - (theta8 θ : ℚ)⁻¹) * (Fintype.card V : ℚ) := by sorry

end RobertsonSeymour1986.GM5
