-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_16
-- name    : RandDelMatroid.Indep.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:32:27.92651+00:00
-- url     : https://prove2.me/theorems/251f7035-2d41-4556-a64a-ae994cf12723
-- title:
--   Lemma 16 — uniqueness of short admissible paths at a graphic node
-- statement:
--   Let $T$ be a clean unordered decomposition tree of a regular matroid $M=(E,\mathcal I)$ with $m\ge2$ elements and minimum circuit size $g$, rooted at $r$, and let $u$ be a graphic node with $M_u=M(G_u)$. Let $H_u$ be $G_u$ minus the parent boundary edges $S_u$; for every child $v$ attached by a 2- or 3-sum and $s\in S_v$ let $P_{Q_v,s}$ be a minimum-cardinality completion; let $A_e=\{e\}$ for $e\in E_u\cap E$, $A_e=P_{Q_v,e}$ for $e\in S_v$, $\ell_u(e)=|A_e|$ and $\ell_u(F)=\sum_{e\in F}\ell_u(e)$. Then for every pair of distinct vertices $x,y$ of $H_u$ there is at most one admissible simple $x$–$y$ path $F$ in $H_u$ with
--
--   $$\ell_u(F)<\frac g2 .$$
--
--   This uniqueness bounds the number of certificates at a graphic node (Lemma 17).
--
--   **Formalization Note** A path is identified with its edge set; for fixed distinct endpoints the edge set of a simple path determines the path.
--
--   Differences from the source:
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: g = min{|C| : C a circuit of M} → hypothesis IsMinCircuitSize M g (some circuit has g elements, every circuit has at least g); reason: the minimum is defined only when M has a circuit; the hypothesis excludes only that undefined case
--   - encoding: M_T is isomorphic to M (Definition 11.4), elements identified → M is a matroid on the tree's element type with M = M_T; reason: the paper identifies M_T with M ('After identifying M_T with M', p. 12); every tree of an abstract M is one of an isomorphic copy on the tree's type
--   - reading: Definition 12.2: for every cographic, non-graphic node v with M_v = M*(G_v), every incident 3-element boundary S_e has a degree-3 vertex of G_v incident to all its edges → IsCleanDecompTree: some multigraph G_v with M_v* = M(G_v) has, for every incident tree edge with |S_e| = 3, a degree-3 vertex (loops counted twice) incident to all edges of S_e; reason: the condition is stated for the underlying graph of the node (§3.2, p. 15: 'a single vertex in the underlying graph'), a graph fixed once per node as in AF22's no-bad-nodes condition; the Lean reads G_v as that chosen graph (existential), not as every graph representing M_v
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 27, Lemma 16 (context: p. 27, §5.3)

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Rooted
import Definitions.Def_RandDelMatroid_Indep_MinCircuitSize

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 16 (p. 27). Let `T` be a clean unordered decomposition tree of a regular matroid `M` with `m ≥ 2` elements and
minimum circuit size `g`, rooted at `r`, and `u` a graphic node, `M_u = M(G_u)` for the multigraph
`G_u = (V, E_u)` with endpoint map `ends`. Let `H_u = G_u - S_u`, let `P` choose minimum-cardinality
completions for the children of `u`, `ℓ_u(e) = |A_e|`, and `ℓ_u(F) = ∑_{e ∈ F} ℓ_u(e)`. For every
pair of distinct vertices `x, y`, there is at most one admissible simple `x`–`y` path `F` in `H_u`
with `ℓ_u(F) < g/2`. -/
theorem lemma_16 {β ι : Type} [Fintype ι] (M : Matroid β) (T : SimpleGraph ι)
    (Mn : ι → Matroid β) (hT : IsCleanDecompTree M T Mn) (hm : 2 ≤ M.E.ncard) (g : ℕ)
    (hg : IsMinCircuitSize M g)
    (r u : ι) (P : β → Set β) (hP : IsMinCompletionChoice T Mn r u P)
    (V : Type) [Fintype V] (ends : β → Sym2 V) (hG : IsGraphicMatroidOf (Mn u) V ends)
    (x y : V) (hxy : x ≠ y) (F₁ F₂ : Set β)
    (hF₁ : IsSimplePathEdges ends x y F₁ ∧ F₁ ⊆ (Mn u).E \ parentBoundary T Mn r u ∧
      IsAdmissible T Mn r u F₁ ∧ pathLength M P F₁ < (g : ℝ) / 2)
    (hF₂ : IsSimplePathEdges ends x y F₂ ∧ F₂ ⊆ (Mn u).E \ parentBoundary T Mn r u ∧
      IsAdmissible T Mn r u F₂ ∧ pathLength M P F₂ < (g : ℝ) / 2) :
    F₁ = F₂ := by sorry

end RandDelMatroid.Indep
