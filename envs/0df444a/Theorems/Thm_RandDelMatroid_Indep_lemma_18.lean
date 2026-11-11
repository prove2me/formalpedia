-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_18
-- name    : RandDelMatroid.Indep.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:32:14.054689+00:00
-- url     : https://prove2.me/theorems/1d17da27-99a5-4748-931f-d9ebd2bcfb40
-- title:
--   Lemma 18 — counting light circuits at a cographic node
-- statement:
--   Let $T$ be a clean unordered decomposition tree of a regular matroid $M=(E,\mathcal I)$ with $m\ge2$ elements and minimum circuit size $g$, rooted at $r$; let $u$ be a cographic node that is not graphic, $m_u=|E_u|$, and $(\hat M_u,w_u)$ the absorption of §5.2 at $u$. Then for every $\alpha\ge1/2$, the number of circuits $\hat D$ of $\hat M_u$ with
--
--   $$|\hat D\cap S_u|\le1\qquad\text{and}\qquad w_u(\hat D)\le\alpha g$$
--
--   is at most $5(2m_u)^{4\alpha}$.
--
--   This count controls the union bound over certificates at cographic nodes (Lemma 19).
--
--   Differences from the source:
--   - generalization: M̂_u, w_u: the specific absorption constructed in §4 with weights adjusted in §5.2 → every (M̂_u, w_u, D ↦ D̂) satisfying IsNodeAbsorption, and every choice of minimum-cardinality completions; reason: the proof uses only cographicity of M̂_u, the circuit bijection, the weight identity w_u(D̂) = |D⁺ \ S_u|, nonnegativity of weights and |Ê_u| = m_u; the paper's construction satisfies these, so the statement specializes to the source's
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: g = min{|C| : C a circuit of M} → hypothesis IsMinCircuitSize M g (some circuit has g elements, every circuit has at least g); reason: the minimum is defined only when M has a circuit; the hypothesis excludes only that undefined case
--   - encoding: M_T is isomorphic to M (Definition 11.4), elements identified → M is a matroid on the tree's element type with M = M_T; reason: the paper identifies M_T with M ('After identifying M_T with M', p. 12); every tree of an abstract M is one of an isomorphic copy on the tree's type
--   - reading: Definition 12.2: for every cographic, non-graphic node v with M_v = M*(G_v), every incident 3-element boundary S_e has a degree-3 vertex of G_v incident to all its edges → IsCleanDecompTree: some multigraph G_v with M_v* = M(G_v) has, for every incident tree edge with |S_e| = 3, a degree-3 vertex (loops counted twice) incident to all edges of S_e; reason: the condition is stated for the underlying graph of the node (§3.2, p. 15: 'a single vertex in the underlying graph'), a graph fixed once per node as in AF22's no-bad-nodes condition; the Lean reads G_v as that chosen graph (existential), not as every graph representing M_v
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 30, Lemma 18 (construction of M̂_u and w_u: p. 26, §5.2; p. 30, §5.4)

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Rooted
import Definitions.Def_RandDelMatroid_Indep_MinCircuitSize

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 18 (p. 30). Let `T` be a clean unordered decomposition tree of a regular matroid `M` with `m ≥ 2` elements and
minimum circuit size `g`, rooted at `r`, and `u` a cographic node that is not graphic, with
`m_u = |E_u|`; let `P` choose minimum-cardinality completions for the children of `u` and
`(M̂_u, w_u)` be the absorption at `u` of §5.2. For every `α ≥ 1/2`, the number of circuits `D̂` of
`M̂_u` with `|D̂ ∩ S_u| ≤ 1` and `w_u(D̂) ≤ αg` is at most `5 (2 m_u)^{4α}`. -/
theorem lemma_18 {β ι : Type} [Fintype ι] [DecidableEq ι] (M : Matroid β) (T : SimpleGraph ι)
    (Mn : ι → Matroid β) (hT : IsCleanDecompTree M T Mn) (hm : 2 ≤ M.E.ncard) (g : ℕ)
    (hg : IsMinCircuitSize M g)
    (r u : ι) (hu : IsCographic (Mn u)) (hng : ¬ IsGraphic (Mn u))
    (P : β → Set β) (hP : IsMinCompletionChoice T Mn r u P)
    (Mh : Matroid (β ⊕ ℕ)) (w : β ⊕ ℕ → ℝ≥0) (corr : Set β → Set (β ⊕ ℕ))
    (hA : IsNodeAbsorption T Mn r u P Mh w corr) (α : ℝ) (hα : 1 / 2 ≤ α) :
    (({Dh : Set (β ⊕ ℕ) | Mh.IsCircuit Dh ∧
        (Dh ∩ Sum.inl '' parentBoundary T Mn r u).ncard ≤ 1 ∧
        setWeight w Dh ≤ α * g}).ncard : ℝ) ≤
      5 * (2 * ((Mn u).E.ncard : ℝ)) ^ (4 * α) := by sorry

end RandDelMatroid.Indep
