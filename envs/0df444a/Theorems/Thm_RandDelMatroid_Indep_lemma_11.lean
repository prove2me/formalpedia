-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_11
-- name    : RandDelMatroid.Indep.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:31:16.055306+00:00
-- url     : https://prove2.me/theorems/d2dc27dc-ee9f-4481-8c17-3b62abb2c394
-- title:
--   Lemma 11 — matroid absorption
-- statement:
--   Let $T$ be a clean unordered decomposition tree of a regular matroid $M$ and $u$ a node. Let $Q_1,\dots,Q_k$ be distinct components attached to $u$ through 2- or 3-sums, with boundary sets $S_1,\dots,S_k$, and let $Q$ be the subtree formed by $u$, these components and their connecting edges. For every $i$ and $s\in S_i$ let $P_{Q_i,s}$ be a completion of $s$ in $Q_i$, and suppose that for every $i$ with $|S_i|=3$
--
--   $$|P_{Q_i,s}|\le\sum_{t\in S_i\setminus\{s\}}|P_{Q_i,t}|\qquad\text{for every } s\in S_i .$$
--
--   Then there is a matroid $\hat M_u=(\hat E_u,\hat{\mathcal I}_u)$ with nonnegative weights $w:\hat E_u\to\mathbb R_{\ge0}$ such that
--
--   1. $E_u\cap E_Q\subseteq\hat E_u$ and $|\hat E_u|=|E_u|$;
--   2. there is a bijection between the circuits $D$ of $M_u$ with $|D\cap S_i|\le1$ for every $i$ and the circuits $\hat D$ of $\hat M_u$, and corresponding circuits satisfy $D\cap(E_u\cap E_Q)=\hat D\cap(E_u\cap E_Q)$ and $w(\hat D)=|D^+|$, where $D^+$ is the expansion of $D$ in $Q$;
--   3. $\hat M_u$ is graphic if $M_u$ is graphic, cographic if $M_u$ is cographic but not graphic, and isomorphic to $R_{10}$ if $M_u$ is isomorphic to $R_{10}$.
--
--   Absorption replaces the child components of a node by weighted elements, reducing the analysis of a node to a weighted graphic, cographic or $R_{10}$ matroid.
--
--   **Formalization Note** The conclusion is `IsAbsorptionData … ∅` with $\hat M_u$ on `β ⊕ ℕ` (old elements tagged `Sum.inl`, fresh labels from `ℕ`).
--
--   Differences from the source:
--   - encoding: a matroid M̂_u = (Ê_u, Î_u) with E_u ∩ E_Q ⊆ Ê_u (new elements unlabelled) → a matroid on β ⊕ ℕ containing Sum.inl '' (E_u ∩ E_Q), with finite ground set; reason: fresh labels for the new elements; Ê_u is finite in the paper (|Ê_u| = |E_u|)
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: M_T is isomorphic to M (Definition 11.4), elements identified → M is a matroid on the tree's element type with M = M_T; reason: the paper identifies M_T with M ('After identifying M_T with M', p. 12); every tree of an abstract M is one of an isomorphic copy on the tree's type
--   - reading: Definition 12.2: for every cographic, non-graphic node v with M_v = M*(G_v), every incident 3-element boundary S_e has a degree-3 vertex of G_v incident to all its edges → IsCleanDecompTree: some multigraph G_v with M_v* = M(G_v) has, for every incident tree edge with |S_e| = 3, a degree-3 vertex (loops counted twice) incident to all edges of S_e; reason: the condition is stated for the underlying graph of the node (§3.2, p. 15: 'a single vertex in the underlying graph'), a graph fixed once per node as in AF22's no-bad-nodes condition; the Lean reads G_v as that chosen graph (existential), not as every graph representing M_v
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 20, Lemma 11

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Absorption

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 11 (matroid absorption, p. 20). Let `T` be a clean unordered decomposition tree of a
regular matroid `M`, `u` a node, and `Q₁, …, Q_k` distinct components attached to `u` through 2- or
3-sums (the neighbours `v ∈ K`, with boundary sets `S_{uv}`); let `Q` be the subtree formed by `u`,
these components and their connecting edges. For every selected `v` and `s ∈ S_{uv}` let `P s` be a
completion of `s` in the component, and suppose that the triangle inequalities
`|P s| ≤ ∑_{t ∈ S_{uv} \ {s}} |P t|` hold whenever `|S_{uv}| = 3`. Then there is a matroid
`M̂_u = (Ê_u, Î_u)` with nonnegative weights `w` satisfying the three properties of Lemma 11
(`IsAbsorptionData … ∅`): `E_u ∩ E_Q ⊆ Ê_u`, `|Ê_u| = |E_u|`; a bijection `D ↦ D̂` from the circuits
of `M_u` meeting each `S_{uv}` in at most one element onto the circuits of `M̂_u`, with
`D ∩ (E_u ∩ E_Q) = D̂ ∩ (E_u ∩ E_Q)` and `w(D̂) = |D⁺|`; and `M̂_u` graphic / cographic / `≅ R10`
when `M_u` is graphic / cographic but not graphic / `≅ R10`. -/
theorem lemma_11 {β ι : Type} [Fintype ι] [DecidableEq ι] (M : Matroid β) (T : SimpleGraph ι)
    (Mn : ι → Matroid β) (hT : IsCleanDecompTree M T Mn) (u : ι) (K : Finset ι)
    (hK : ∀ v ∈ K, T.Adj u v ∧ (edgeBoundary Mn u v).Nonempty) (P : β → Set β)
    (hP : ∀ v ∈ K, ∀ s ∈ edgeBoundary Mn u v,
      IsCompletion T Mn (attachedComp T u v) (edgeBoundary Mn u v) s (P s))
    (htri : ∀ v ∈ K, (edgeBoundary Mn u v).ncard = 3 → ∀ s ∈ edgeBoundary Mn u v,
      (P s).ncard ≤ ∑ᶠ t ∈ edgeBoundary Mn u v \ {s}, (P t).ncard) :
    ∃ (Mh : Matroid (β ⊕ ℕ)) (w : β ⊕ ℕ → ℝ≥0) (corr : Set β → Set (β ⊕ ℕ)),
      IsAbsorptionData T Mn u K P ∅ Mh w corr := by sorry

end RandDelMatroid.Indep
