-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_19
-- name    : RandDelMatroid.Indep.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:32:11.937496+00:00
-- url     : https://prove2.me/theorems/6aafb70f-5267-4b18-80eb-75a8ac202829
-- title:
--   Lemma 19 — certificates at cographic nodes
-- statement:
--   Let $T$ be a clean unordered decomposition tree of a regular matroid $M=(E,\mathcal I)$ with $m\ge2$ elements and minimum circuit size $g$, rooted at $r$; let $u$ be a cographic node that is not graphic and $m_u=|E_u|$. Then there is a collection $\mathcal W_u$ of sets such that
--
--   1. every $W\in\mathcal W_u$ is a subset of $E_{Q_u}\setminus S_u$ with $|W|\ge g/2$;
--   2. for every $R\subseteq E$, if $u$ is not $R$-good and all its children are $R$-good, then some $W\in\mathcal W_u$ satisfies $W\subseteq R$.
--
--   Moreover, if $R$ is the set returned by Algorithm 1 on $M$, then
--
--   $$\Pr[\exists\,W\in\mathcal W_u \text{ with } W\subseteq R]\ \le\ \frac{160\,m_u^4}{m^{20}} .$$
--
--   Together with Lemma 17 and the $R_{10}$ case, this gives the per-node bound $160m_u^4/m^{20}$ summed over the at most $2m$ nodes in the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: g = min{|C| : C a circuit of M} → hypothesis IsMinCircuitSize M g (some circuit has g elements, every circuit has at least g); reason: the minimum is defined only when M has a circuit; the hypothesis excludes only that undefined case
--   - encoding: M_T is isomorphic to M (Definition 11.4), elements identified → M is a matroid on the tree's element type with M = M_T; reason: the paper identifies M_T with M ('After identifying M_T with M', p. 12); every tree of an abstract M is one of an isomorphic copy on the tree's type
--   - reading: Definition 12.2: for every cographic, non-graphic node v with M_v = M*(G_v), every incident 3-element boundary S_e has a degree-3 vertex of G_v incident to all its edges → IsCleanDecompTree: some multigraph G_v with M_v* = M(G_v) has, for every incident tree edge with |S_e| = 3, a degree-3 vertex (loops counted twice) incident to all edges of S_e; reason: the condition is stated for the underlying graph of the node (§3.2, p. 15: 'a single vertex in the underlying graph'), a graph fixed once per node as in AF22's no-bad-nodes condition; the Lean reads G_v as that chosen graph (existential), not as every graph representing M_v
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 31, Lemma 19

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Rooted
import Definitions.Def_RandDelMatroid_Indep_MinCircuitSize
import Definitions.Def_RandDelMatroid_Indep_RandomDelete

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 19 (p. 31). Let `T` be a clean unordered decomposition tree of a regular matroid `M` with
`m ≥ 2` elements and minimum circuit size `g`, rooted at `r`, and `u` a cographic node that is not
graphic, with `m_u = |E_u|`. There is a collection `W_u` of sets such that
1. every `W ∈ W_u` is a subset of `E_{Q_u} \ S_u` with `|W| ≥ g/2`;
2. for every `R ⊆ E`, if `u` is not `R`-good and all its children are `R`-good, some `W ∈ W_u`
   satisfies `W ⊆ R`;
and for the set `R` returned by Algorithm 1, `Pr[∃ W ∈ W_u, W ⊆ R] ≤ 160 m_u⁴ / m^20`. -/
theorem lemma_19 {β ι : Type} [Fintype ι] (M : Matroid β) [M.Finite] (T : SimpleGraph ι)
    (Mn : ι → Matroid β) (hT : IsCleanDecompTree M T Mn) (hm : 2 ≤ M.E.ncard) (g : ℕ)
    (hg : IsMinCircuitSize M g) (r u : ι) (hu : IsCographic (Mn u)) (hng : ¬ IsGraphic (Mn u)) :
    ∃ W : Set (Set β),
      (∀ X ∈ W, X ⊆ groundOf Mn (below T r u) \ parentBoundary T Mn r u ∧
        (g : ℝ) / 2 ≤ (X.ncard : ℝ)) ∧
      (∀ R : Set β, R ⊆ M.E → ¬ IsRGood T Mn r g R u →
        (∀ v, IsChild T r u v → IsRGood T Mn r g R v) → ∃ X ∈ W, X ⊆ R) ∧
      alg1Prob M g {R | ∃ X ∈ W, X ⊆ R} ≤
        160 * ((Mn u).E.ncard : ℝ) ^ 4 / (M.E.ncard : ℝ) ^ 20 := by sorry

end RandDelMatroid.Indep
