-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Minimax_result_2_7
-- name    : RobertsonSeymour1991.GM10.Minimax.result_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:01:42.432694+00:00
-- url     : https://prove2.me/theorems/9034ca92-e304-42c8-a995-16d414ca13e1
-- title:
--   (2.7), p. 157 — a set satisfying the first two axioms is a tangle iff it contains every (K_e, G\e) with |e| < θ
-- statement:
--   Let $\theta\ge1$ and let $\mathcal T$ be a set of separations of a hypergraph $G$, each of order $<\theta$, satisfying the first and second tangle axioms. Then $\mathcal T$ is a tangle of order $\theta$ if and only if
--
--   $$(K_e,\;G\setminus e)\in\mathcal T\quad\text{for every edge }e\text{ of }G\text{ of size }<\theta,$$
--
--   where $K_e$ is the hypergraph formed by $e$ and its ends.
--
--   It reduces the third tangle axiom to a check on single edges, which is how tangles are built from biases in claim (1) of the proof of (4.3).
--
--   **Formalization Note** All hypergraphs are finite (p. 154), so the vertex type $V$ and the edge type $E$ carry `Finite` instances. The bound $\theta\ge1$ is the standing assumption of the tangle definition (p. 154, "let $\theta\ge1$ be an integer"); without it the left side would be false and the right side vacuous at $\theta=0$. The two axioms are written out as hypotheses.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 157, (2.7); θ ≥ 1 from p. 154

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Tangle

namespace RobertsonSeymour1991.GM10.Minimax

/-- (2.7), p. 157: let `𝒯` be a set of separations of `G`, each of order `< θ`, satisfying the first and
second tangle axioms (`θ ≥ 1` is the standing assumption of the tangle definition, p. 154). Then `𝒯` is a
tangle (of order `θ`) if and only if `(K_e, G\e) ∈ 𝒯` for every `e ∈ E(G)` of size `< θ`. -/
theorem result_2_7 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ) (hθ : 1 ≤ θ)
    (𝒯 : Set (G.Sub × G.Sub))
    (hsep : ∀ p ∈ 𝒯, Hypergraph.IsSeparation p.1 p.2 ∧ Hypergraph.order p.1 p.2 < θ)
    (hfirst : ∀ A B : G.Sub, Hypergraph.IsSeparation A B → Hypergraph.order A B < θ →
      (A, B) ∈ 𝒯 ∨ (B, A) ∈ 𝒯)
    (hsecond : ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, ∀ p₃ ∈ 𝒯, (p₁.1.union p₂.1).union p₃.1 ≠ Hypergraph.Sub.top G) :
    G.IsTangle θ 𝒯 ↔ ∀ e : E, G.size e < θ → (G.edgeSub e, G.deleteEdges {e}) ∈ 𝒯 := by sorry

end RobertsonSeymour1991.GM10.Minimax
