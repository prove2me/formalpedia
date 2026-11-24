-- Prove2me | Theorems.Thm_SendSplit_Existence_Supplement_theorem3_planar_extreme_flows
-- name    : SendSplit.Existence.Supplement.theorem3_planar_extreme_flows
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:48:00.386414+00:00
-- url     : https://prove2.me/theorems/5c45d14a-8d71-4d7d-b859-bfbf9982a398
-- title:
--   Theorem 3 — extreme flows in planar networks (corrected: allow the empty circular block)
-- statement:
--   Let $(G,r)$ be a finite connected directed network with real demands, embedded in the plane, and let $x$ be an extreme flow, meaning that its nonzero-flow arc support is an undirected forest. No cost or minimum-cost hypothesis is required. Then a minimal tree containing the whole support exists.
--
--   Every such induced tree $T$ has the following properties for every demand root $\sigma$ with $r_\sigma\ne0$, every nonempty face set $D$, every compatible choice of its face-star augmentation and clockwise order $o$, and every tree vertex $i$. Write $S=\{v\in D:i\in\sigma:v\}$, using endpoint-inclusive undirected paths.
--
--   1. The separated set is a circular block:
--   $$S=\varnothing\quad\text{or}\quad S=[\alpha,\beta)_o\text{ for some }\alpha,\beta\in D.$$
--   2. For every representation $S=[\alpha,\beta)_o\ne D$, if $i$ is an internal node of that interval, then
--   $$\forall u\in[\alpha,i)_o\ \forall v\in[i,\beta)_o,\qquad i\in u:v.$$
--
--   The theorem also makes explicit the existence of a face augmentation for every nonempty face set and a compatible clockwise order for every augmentation. Singleton face sets use their unique order. Thus the geometric-order conditions do not restrict the source domain. This companion theorem describes the planar structure of extreme flows used to restrict the send-and-split subproblems; it is not used in the proof of the referenced goal, Theorem 1.
--
--   **Formalization Note** Equal endpoints mean the entire face set. Empty separated sets use an additional empty block, correcting the printed boundary omission. The clockwise coordinates are orientation-preserving ambient coordinate changes and do not assume straight original arcs. Every minimal containing tree and every compatible augmentation and order is covered; paths ignore arc direction and include their endpoints.
--
--   Differences from the source:
--   - correction: property 1° requires an endpoint interval [α,β), although these intervals never represent the empty set → property 1° permits a distinguished empty circular block in addition to the printed endpoint intervals; [α,α)=D is retained; reason: a face can miss the separated branch; the alternating-four-vertices proof on p. 646 and the empty-piece statement on p. 650 support this boundary completion; no graph, flow or face case is excluded
--   - reading: each extreme flow induces a tree, with clockwise order supplied by the face-star construction → existence of a minimal containing tree, of a face augmentation for each nonempty face set, and of a compatible geometric clockwise enumeration for every augmentation are explicit conclusions; reason: the source constructs these objects before giving the two properties; stating existence prevents hidden geometric regularity or vacuous order hypotheses
--   - encoding: undirected paths, face sets and subintervals in a connected planar network → published real flows on Fin n, explicit arc-labelled tree subgraphs, simple continuous plane curves, complementary regions, and finite cyclic enumerations with arbitrary starting cuts; reason: these retain the same finite loopless networks, weak connectivity, repeated face boundaries and antiparallel edge identities; all choices and both endpoints of paths are retained
--   - reading: an internal node of [α,β) ⊂ Dᵗ in property 2° → the interval is proper and the node is neither α nor the clockwise predecessor of β, in the original face order; reason: the source proof chooses a vertex outside the interval; the excluded terminal endpoint β is not an included end node
-- source:
--   Erickson, Monma and Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Mathematics of Operations Research 12(4) (1987), DOI 10.1287/moor.12.4.634, p. 646, Theorem 3 and its proof (PDF 14); p. 650, empty-piece convention (PDF 18)

import Mathlib
import Definitions.Def_SendSplit_Existence_Supplement_FaceStars
import Definitions.Def_SendSplit_Existence_Supplement_InducedTrees

set_option autoImplicit false

namespace SendSplit.Existence.Supplement

/-- Erickson–Monma–Veinott (1987), Theorem 3, p. 646 (PDF 14).
The empty block completes the printed interval convention, supported by the
alternating-four-vertices argument and the empty-piece convention on p. 650.
All other conclusions are retained. The implicit face-star and clockwise-order
constructions are explicit existence conclusions, never extra premises. -/
theorem theorem3_planar_extreme_flows {n : ℕ} (G : ArcGraph n)
    (r : Fin n → ℝ) (P : Drawing G) (hconn : IsConnected G)
    (x : Fin n → Fin n → ℝ) (hx : IsExtremeFlow G r x) :
    (∃ T : TreeSubgraph G, IsInducedTree x T) ∧
    ∀ F : PlaneFace P, (faceSet P r F).Nonempty →
      Nonempty (FaceAugmentation P r F) ∧
      ∀ U : FaceAugmentation P r F,
        (∃ o : CircularOrder (faceSet P r F), IsClockwise U o) ∧
        ∀ o : CircularOrder (faceSet P r F), IsClockwise U o →
          ∀ T : TreeSubgraph G, IsInducedTree x T →
            ∀ σ : Fin n, r σ ≠ 0 →
              ∀ i ∈ T.nodes,
                IsCircularBlock o (separated T σ i (faceSet P r F)) ∧
                ∀ a b k : {v // v ∈ faceSet P r F}, k.val = i →
                  separated T σ i (faceSet P r F) = circularInterval o a b →
                  circularInterval o a b ≠ faceSet P r F → IsInternal o a b k →
                    SeparatesSets T i (circularInterval o a k) (circularInterval o k b) := by sorry

end SendSplit.Existence.Supplement
