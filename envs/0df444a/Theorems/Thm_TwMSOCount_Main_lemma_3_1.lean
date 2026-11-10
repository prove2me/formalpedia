-- Prove2me | Theorems.Thm_TwMSOCount_Main_lemma_3_1
-- name    : TwMSOCount.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:45:34.325202+00:00
-- url     : https://prove2.me/theorems/b7f9c764-1f55-4321-b181-94f50901244f
-- title:
--   Lemma 3.1 — a one-step description reconstructs $H$ and splits its partial weight
-- statement:
--   Let $(H,\chi,\iota)$ be a well-formed colored $B$-boundaried graph, $S\subseteq V(H)$, $S_{\mathrm{int}} = S\setminus\partial H$, and $\eta : N\to S_{\mathrm{int}}$ a bijection from a set $N$ of new labels ($N\cap B=\emptyset$), giving $\iota^+ = \iota\cup\eta$ on $B\cup N$. Let $D_1,\dots,D_p$ be the components of $H-S$ in any order, $H_i = H[D_i\cup S]-F_S$ the pieces with label sets $B_i$ (the labels of $\iota^+$ lying in $D_i\cup S$), $F_S = E(H[S])$ and $F$ its label pattern.
--
--   **Lemma.** (i) Glue the pieces onto the edgeless graph on $S$ (labels $J$, colors and output labels of $H$) by identifying vertices with a common label, add the local edges $\iota^+(F)$ and forget $N$: the result is isomorphic to $(H,\chi,\iota)$ by an isomorphism preserving colors, boundary labels and output labels. (ii)
--   $$W_B(H,\chi) = \omega_\chi(F_S)\prod_{v\in S_{\mathrm{int}}}\lambda_{\chi(v)}\prod_{i=1}^p W_{B_i}(H_i,\chi).$$
--
--   The local edges and the pieces partition the edges of $H$; this is what makes each weight factor be charged exactly once in a recursive description.
--
--   Differences from the source:
--   - encoding: colored B-boundaried graph with injective boundary map, independently of output labels → BGraph with BoundaryWF; reason: Table 2 and construction terms act on structural graphs; distinct output labels are required only for recursive descriptions
--   - reading: glue the pieces; if p = 0 start instead from the edgeless graph on S → always glue the pieces onto the edgeless graph on S, from the left; reason: gluing that edgeless graph to a piece, which contains all of S with the same labels, colors and output labels, gives the piece again; for p = 0 it is the source's start
--   - encoding: the result is (H, χ, ι), output labels included → BGraph.IsoOut (result) H; reason: the glued graph lives on a new vertex type; IsoOut preserves adjacency, colors, boundary labels and internal output labels
--   - encoding: pieces H_1, …, H_p → Ds.map (piece (extend H N η) S) for a duplicate-free list Ds of the component vertex sets; reason: any order of the pieces, as in the source
--   - generalization: the nonempty finite color set C of Section 2 → the structural assertion also permits r = 0; reason: with no colors a coloring exists only on the empty vertex type; the empty case is valid, or the positive-internal-size hypotheses exclude it; every source instance is retained
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Lemma 3.1, p. 5 (PDF 6)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator

namespace TwMSOCount.Main

theorem lemma_3_1 {r k : ℕ} (w : Weights r) (H : BGraph r k) (hH : H.WF)
    (S : Finset H.V) (N : Finset (Lab k)) (η : N → H.V) (hη : IsLabelAssignment H S N η)
    (Ds : List (Finset H.V)) (hDs : Ds.Nodup) (hDs' : Ds.toFinset = BGraph.comps H.G S) :
    BGraph.IsoOut
        (BGraph.forgetSet
          (BGraph.addEdges (glueAll (sepBase (extend H N η) S) (Ds.map (piece (extend H N η) S)))
            (labelPattern (extend H N η) (labelsIn (extend H N η) S))) N) H ∧
      BGraph.pw w H = w.omega H.col (localEdges H S) * (∏ v ∈ S \ H.bdry, w.vtx (H.col v)) *
        ((Ds.map (piece (extend H N η) S)).map (BGraph.pw w)).prod := by sorry

end TwMSOCount.Main
