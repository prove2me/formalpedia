-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_14
-- name    : RandDelMatroid.Indep.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:32:08.438346+00:00
-- url     : https://prove2.me/theorems/76fc0ef3-2f35-4a5e-8b3e-16974c3f627a
-- title:
--   Lemma 14 — short completions are unique
-- statement:
--   Let $T$ be a clean unordered decomposition tree of a regular matroid $M=(E,\mathcal I)$ with $m\ge2$ elements and minimum circuit size $g$, rooted at a node $r$. For every node $u$ and every $s\in S_u$ there is at most one completion $P$ of $s$ in $Q_u$ with
--
--   $$|P|<\frac g2 .$$
--
--   This uniqueness pins down the child projections of a surviving circuit in the proof of Lemma 15.
--
--   Differences from the source:
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: g = min{|C| : C a circuit of M} → hypothesis IsMinCircuitSize M g (some circuit has g elements, every circuit has at least g); reason: the minimum is defined only when M has a circuit; the hypothesis excludes only that undefined case
--   - encoding: M_T is isomorphic to M (Definition 11.4), elements identified → M is a matroid on the tree's element type with M = M_T; reason: the paper identifies M_T with M ('After identifying M_T with M', p. 12); every tree of an abstract M is one of an isomorphic copy on the tree's type
--   - reading: Definition 12.2: for every cographic, non-graphic node v with M_v = M*(G_v), every incident 3-element boundary S_e has a degree-3 vertex of G_v incident to all its edges → IsCleanDecompTree: some multigraph G_v with M_v* = M(G_v) has, for every incident tree edge with |S_e| = 3, a degree-3 vertex (loops counted twice) incident to all edges of S_e; reason: the condition is stated for the underlying graph of the node (§3.2, p. 15: 'a single vertex in the underlying graph'), a graph fixed once per node as in AF22's no-bad-nodes condition; the Lean reads G_v as that chosen graph (existential), not as every graph representing M_v
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 25, Lemma 14 (standing assumptions of §5.1)

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Rooted
import Definitions.Def_RandDelMatroid_Indep_MinCircuitSize

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 14 (p. 25). Let `T` be a clean unordered decomposition tree of a regular matroid `M` with `m ≥ 2` elements and
minimum circuit size `g`, rooted at `r`. For every node `u` and every `s ∈ S_u`, there is at most
one completion `P` of `s` in `Q_u` with `|P| < g/2`. -/
theorem lemma_14 {β ι : Type} [Fintype ι] (M : Matroid β) (T : SimpleGraph ι)
    (Mn : ι → Matroid β) (hT : IsCleanDecompTree M T Mn) (hm : 2 ≤ M.E.ncard) (g : ℕ)
    (hg : IsMinCircuitSize M g)
    (r u : ι) (s : β) (hs : s ∈ parentBoundary T Mn r u) (P P' : Set β)
    (hP : IsCompletion T Mn (below T r u) (parentBoundary T Mn r u) s P)
    (hP' : IsCompletion T Mn (below T r u) (parentBoundary T Mn r u) s P')
    (hPg : (P.ncard : ℝ) < (g : ℝ) / 2) (hP'g : (P'.ncard : ℝ) < (g : ℝ) / 2) :
    P = P' := by sorry

end RandDelMatroid.Indep
