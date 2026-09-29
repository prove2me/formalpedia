-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_balanced_separation_of_set
-- name    : RobertsonSeymour1986.GM5.balanced_separation_of_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:04:28.875384+00:00
-- url     : https://prove2.me/theorems/d18aea98-0d51-48f9-ac84-222e0ccf34e5
-- title:
--   (7.2) Separation of order at most $\theta_7$ balanced with respect to a vertex set $X$
-- statement:
--   Let $\theta\ge 6$ be even, let $G$ be a finite graph with no $\theta$-grid minor, and let $X\subseteq V(G)$. Then $G$ has a separation $(V_1,V_2)$ such that
--
--   $$|V_1\cap V_2|\le\theta_7\quad\text{and}\quad |(V_1-V_2)\cap X|,\ |(V_2-V_1)\cap X|\le (1-\theta_8^{-1})\,|X|.$$
--
--   Separations balanced with respect to a vertex set are what the inductive construction of a tree-decomposition in (7.3) consumes.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (7.2), p. 107 (PDF p. 16); DOI 10.1016/0095-8956(86)90030-4

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_NoGridMinor
import Definitions.Def_RobertsonSeymour1986_GM5_Params
import Definitions.Def_RobertsonSeymour1986_GM5_IsSeparation

namespace RobertsonSeymour1986.GM5

/-- (7.2): for any vertex set `X` of a graph without a θ-grid minor there is a separation of order
at most `θ₇` splitting `X` in the ratio `(1 − θ₈^{−1})`.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), (7.2), p. 107 (PDF p. 16): "If G ∈ 𝓕_θ and X ⊆ V(G) then G has a separation (V₁, V₂) such
that |V₁ ∩ V₂| ≤ θ₇ and |(V₁ − V₂) ∩ X|, |(V₂ − V₁) ∩ X| ≤ (1 − θ₈^{−1})|X|."

**Formalization Note** The standing assumption of p. 95 (PDF p. 4), "θ is a fixed even integer with θ ≥ 6", is the pair
of hypotheses `Even θ`, `6 ≤ θ`; "G ∈ 𝓕_θ" is `NoGridMinor θ G`. The bound is compared in `ℚ`. -/
theorem balanced_separation_of_set {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (θ : ℕ) (hθe : Even θ) (hθ6 : 6 ≤ θ) (hG : NoGridMinor θ G) (X : Finset V) :
    ∃ V₁ V₂ : Finset V, IsSeparation G V₁ V₂ ∧ (V₁ ∩ V₂).card ≤ theta7 θ ∧
      (((V₁ \ V₂) ∩ X).card : ℚ) ≤ (1 - (theta8 θ : ℚ)⁻¹) * (X.card : ℚ) ∧
      (((V₂ \ V₁) ∩ X).card : ℚ) ≤ (1 - (theta8 θ : ℚ)⁻¹) * (X.card : ℚ) := by sorry

end RobertsonSeymour1986.GM5
