-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_15
-- name    : RandDelMatroid.Indep.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:32:15.509204+00:00
-- url     : https://prove2.me/theorems/3aa6cf10-f3b7-4eec-a1b3-13f8448f1c32
-- title:
--   Lemma 15 — a failing node with good children has a heavy surviving circuit
-- statement:
--   Let $T$ be a clean unordered decomposition tree of a regular matroid $M=(E,\mathcal I)$ with $m\ge2$ elements and minimum circuit size $g$, rooted at $r$. Let $R\subseteq E$ and let $u$ be a node; let $(\hat M_u,w_u)$ be the absorption of §5.2 at $u$ (all children attached through 2- or 3-sums absorbed with minimum-cardinality completions, the parent boundary $S_u$ kept with weight $0$). Suppose that $u$ is not $R$-good but all its children are $R$-good. Then $\hat M_u$ contains a circuit $\hat D$ with corresponding circuit $D$ of $M_u$ such that
--
--   1. $D$ meets every child boundary $S_v$ in at most one element;
--   2. $|D\cap S_u|\le1$, $D^+\setminus S_u\subseteq R$, and $w_u(\hat D)\ge g/2$;
--   3. if $D\cap S_u=\emptyset$, then $w_u(\hat D)\ge g$.
--
--   The lemma turns the failure of $R$-goodness into the survival of a heavy expansion, which the certificates of Lemmas 17 and 19 capture.
--
--   Differences from the source:
--   - generalization: M̂_u, w_u: the specific absorption constructed in §4 (Lemmas 12, 13, §4.4) with weights adjusted in §5.2 → every (M̂_u, w_u, D ↦ D̂) satisfying IsNodeAbsorption (the properties of Lemma 11 for the §5.2 children and completions, w_u(D̂) = |D⁺ \ S_u|, weight 0 on S_u), and every choice of minimum-cardinality completions; reason: the proof uses only these properties; the paper's construction satisfies them (Lemma 11 and p. 26), so the statement specializes to the source's
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: g = min{|C| : C a circuit of M} → hypothesis IsMinCircuitSize M g (some circuit has g elements, every circuit has at least g); reason: the minimum is defined only when M has a circuit; the hypothesis excludes only that undefined case
--   - encoding: M_T is isomorphic to M (Definition 11.4), elements identified → M is a matroid on the tree's element type with M = M_T; reason: the paper identifies M_T with M ('After identifying M_T with M', p. 12); every tree of an abstract M is one of an isomorphic copy on the tree's type
--   - reading: Definition 12.2: for every cographic, non-graphic node v with M_v = M*(G_v), every incident 3-element boundary S_e has a degree-3 vertex of G_v incident to all its edges → IsCleanDecompTree: some multigraph G_v with M_v* = M(G_v) has, for every incident tree edge with |S_e| = 3, a degree-3 vertex (loops counted twice) incident to all edges of S_e; reason: the condition is stated for the underlying graph of the node (§3.2, p. 15: 'a single vertex in the underlying graph'), a graph fixed once per node as in AF22's no-bad-nodes condition; the Lean reads G_v as that chosen graph (existential), not as every graph representing M_v
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 26, Lemma 15 (construction of M̂_u and w_u: p. 26, §5.2)

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Rooted
import Definitions.Def_RandDelMatroid_Indep_MinCircuitSize

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 15 (p. 26). Let `T` be a clean unordered decomposition tree of a regular matroid `M` with `m ≥ 2` elements and
minimum circuit size `g`, rooted at `r`; let `R ⊆ E` and let `u` be a node. Let `P` choose
minimum-cardinality completions for the children of `u`, and let `(M̂_u, w_u, D ↦ D̂)` be the
absorption at `u` of §5.2. If `u` is not `R`-good but all its children are `R`-good, then `M̂_u`
contains a circuit `D̂` with corresponding circuit `D` of `M_u` such that
1. `D` meets every child boundary `S_v` in at most one element;
2. `|D ∩ S_u| ≤ 1`, `D⁺ \ S_u ⊆ R` and `w_u(D̂) ≥ g/2`;
3. if `D ∩ S_u = ∅` then `w_u(D̂) ≥ g`. -/
theorem lemma_15 {β ι : Type} [Fintype ι] [DecidableEq ι] (M : Matroid β) (T : SimpleGraph ι)
    (Mn : ι → Matroid β) (hT : IsCleanDecompTree M T Mn) (hm : 2 ≤ M.E.ncard) (g : ℕ)
    (hg : IsMinCircuitSize M g)
    (R : Set β) (hR : R ⊆ M.E) (r u : ι) (P : β → Set β) (hP : IsMinCompletionChoice T Mn r u P)
    (Mh : Matroid (β ⊕ ℕ)) (w : β ⊕ ℕ → ℝ≥0) (corr : Set β → Set (β ⊕ ℕ))
    (hA : IsNodeAbsorption T Mn r u P Mh w corr)
    (hu : ¬ IsRGood T Mn r g R u) (hch : ∀ v, IsChild T r u v → IsRGood T Mn r g R v) :
    ∃ D : Set β, (Mn u).IsCircuit D ∧ Mh.IsCircuit (corr D) ∧
      (∀ v, IsChild T r u v → (D ∩ edgeBoundary Mn u v).ncard ≤ 1) ∧
      (D ∩ parentBoundary T Mn r u).ncard ≤ 1 ∧
      expansion D (selBoundary Mn u (sumChildren T Mn r u)) P \ parentBoundary T Mn r u ⊆ R ∧
      (g : ℝ) / 2 ≤ setWeight w (corr D) ∧
      (D ∩ parentBoundary T Mn r u = ∅ → (g : ℝ) ≤ setWeight w (corr D)) := by sorry

end RandDelMatroid.Indep
