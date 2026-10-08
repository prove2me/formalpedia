-- Prove2me | Theorems.Thm_RobertsonSeymour1991_GM10_Structure_result_11_2
-- name    : RobertsonSeymour1991.GM10.Structure.result_11_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:13:53.308892+00:00
-- url     : https://prove2.me/theorems/9a7ee543-66f6-4672-ab0a-8dec1f456328
-- title:
--   (11.2), pp. 185–186 — for |Z| = 3θ − 2, a balanced separation of order < θ or a Z-small location with design in 𝒮
-- statement:
--   Let $G$ be a finite hypergraph, let $\theta \ge 1$, let $\mathcal S$ be a class of designs that is $\theta$-pervasive in $G$, and let $Z \subseteq V(G)$ with $|Z| = 3\theta - 2$. Then either
--
--   1. there is a separation $(A, B)$ of $G$ of order $< \theta$ with
--   $$|(Z \cup V(A)) \cap V(B)|,\ |(Z \cup V(B)) \cap V(A)| \le 3\theta - 3,$$
--   or
--   2. there is a location $\{(A_1, B_1), \dots, (A_k, B_k)\}$ in $G$, with design in $\mathcal S$, such that for $1 \le i \le k$,
--   $$|Z \cap V(A_i)| \le |V(A_i \cap B_i)| < \theta.$$
--
--   This dichotomy is the inductive step of the structure theorem: either $Z$ can be split by a small separation, or a location from $\mathcal S$ captures $Z$.
--
--   **Formalization Note** Designs are $G$-designs and "$\theta$-pervasive" is `IsPervasive θ 𝒮` (see the Design definition). "A location in $G$" is `IsLocationIn (Sub.top G)`. Since $\theta \ge 1$, the natural-number expressions $3\theta - 2$ and $3\theta - 3$ are exact (at $\theta = 1$ the bound in (1) is $0$, with $|Z| = 1$).
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), pp. 185–186, (11.2)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_TreeDecomposition
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_Design

namespace RobertsonSeymour1991.GM10.Structure

theorem result_11_2 {V E : Type} [Finite V] [Finite E] (G : Hypergraph V E) (θ : ℕ) (hθ : 1 ≤ θ)
    (𝒮 : Set G.Design) (h𝒮 : Hypergraph.IsPervasive θ 𝒮) (Z : Set V) (hZ : Z.ncard = 3 * θ - 2) :
    (∃ A B : G.Sub, Hypergraph.IsSeparation A B ∧ Hypergraph.order A B < θ ∧
        ((Z ∪ A.verts) ∩ B.verts).ncard ≤ 3 * θ - 3 ∧
        ((Z ∪ B.verts) ∩ A.verts).ncard ≤ 3 * θ - 3) ∨
    (∃ L : Set (G.Sub × G.Sub), Hypergraph.IsLocationIn (Hypergraph.Sub.top G) L ∧
        Hypergraph.locationDesign (Hypergraph.Sub.top G) L ∈ 𝒮 ∧
        ∀ p ∈ L, (Z ∩ p.1.verts).ncard ≤ Hypergraph.order p.1 p.2 ∧
          Hypergraph.order p.1 p.2 < θ) := by sorry

end RobertsonSeymour1991.GM10.Structure
