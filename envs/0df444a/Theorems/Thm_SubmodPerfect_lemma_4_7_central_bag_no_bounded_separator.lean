-- Prove2me | Theorems.Thm_SubmodPerfect_lemma_4_7_central_bag_no_bounded_separator
-- name    : SubmodPerfect.lemma_4_7_central_bag_no_bounded_separator
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:12.954347+00:00
-- url     : https://prove2.me/theorems/9873372d-2ca5-4086-96b4-6f92edfa0466
-- title:
--   Lemma 4.7 — central bags of loosely laminar star separations have no $(d-1)$-bounded balanced separator
-- statement:
--   Throughout, the common assumptions of Section 4 hold: $c\in[\tfrac12,1)$, $d\ge\delta\ge1$ are integers, $G$ is a finite graph in which every vertex has degree at most $\delta$, $w:V(G)\to[0,1]$ is a weight function with $w(G)=1$, and $G$ has no $d$-bounded $(w,c)$-balanced separator.
--
--   Let $\mathcal S=(S_1,\dots,S_s)$ be a loosely laminar sequence of star separations of $G$, where $S_i$ has center (and anchor) $v_i$ and the $v_i$ are distinct. Let $\beta_{\mathcal S}=\bigcap_i(B(S_i)\cup C(S_i))$ be its central bag and $w_{\mathcal S}$ its weight function. Then
--
--   $$\beta_{\mathcal S}\ \text{has no }(d-1)\text{-bounded }(w_{\mathcal S},c)\text{-balanced separator,}$$
--
--   where balls and components are those of the induced subgraph $G[\beta_{\mathcal S}]$.
--
--   Passing to the central bag thus costs at most one unit of the boundedness parameter; Lemma 4.8 iterates this along the dimension of the star covering.
--
--   Differences from the source:
--   - generalization: G has maximum degree δ → every vertex of G has degree at most δ (δ ≥ 1); reason: the source's statement is the case where δ is the maximum degree; for a graph of maximum degree δ′ ≤ δ the hypotheses on d and the conclusion only weaken with δ, so the source's statement at δ′ implies the Lean one
--   - encoding: a sequence of star separations, each with its center as anchor → a list of pairs (separation, center) with distinct centers; reason: every vertex is the center of at most one separation; same instances
--   - encoding: induced subgraphs, paths and weight functions w : V(G) → [0, 1] → vertex sets (Finset), induced paths as lists, and w : V → ℝ with values in [0, 1] on the vertex set; reason: Lean convention; same instances
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Lemma 4.7, p.12 (common assumptions for Section 4, p.10)

import Mathlib
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels
import Definitions.Def_SubmodPerfect_StarSeparations

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Lemma 4.7, p.12.

Let `𝒮 = (S₁, …, S_s)` be a loosely laminar sequence of star separations such that every vertex
is the center of at most one separation in `𝒮`, and let `β_𝒮` be its central bag. Then `β_𝒮`
has no `(d − 1)`-bounded `(w_𝒮, c)`-balanced separator.

**Formalization Note.** The common assumptions of Section 4 (p.10) are explicit hypotheses: `c ∈ [1/2, 1)`,
positive integers `d ≥ δ`, a weight function `w : V → [0, 1]` with `w(G) = 1`, maximum degree
(at most) `δ`, and no `d`-bounded `(w, c)`-balanced separator. The sequence is a list of pairs `(Sᵢ, vᵢ)`, `vᵢ` the center
(and anchor) of `Sᵢ`; "every vertex is the center of at most one separation" is the
distinctness of the `vᵢ`. Balls and components are those of `G[β_𝒮]`. -/
theorem lemma_4_7_central_bag_no_bounded_separator {V : Type*} [Fintype V]
    (c : ℝ) (hc : 1 / 2 ≤ c ∧ c < 1) (d δ : ℕ) (hδ : 1 ≤ δ) (hdδ : δ ≤ d)
    (G : SimpleGraph V) (w : V → ℝ) (hw : IsWeightFunctionOn w Finset.univ)
    (hw1 : wsum w Finset.univ = 1) (hdeg : MaxDegreeLe G δ)
    (hnosep : ¬ HasBoundedBalancedSepIn G Finset.univ w c d)
    (l : List (Sep V × V)) (hstar : ∀ p ∈ l, IsStarSepCenteredIn G Finset.univ p.1 p.2)
    (hlam : IsLooselyLaminar l) (hcenter : (l.map Prod.snd).Nodup) :
    ¬ HasBoundedBalancedSepIn G (centralBag Finset.univ l) (centralWeight w l) c (d - 1) := by sorry

end SubmodPerfect
