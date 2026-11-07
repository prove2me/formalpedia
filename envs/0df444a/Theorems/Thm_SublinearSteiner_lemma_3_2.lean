-- Prove2me | Theorems.Thm_SublinearSteiner_lemma_3_2
-- name    : SublinearSteiner.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:44:37.732232+00:00
-- url     : https://prove2.me/theorems/972624f6-d891-46e9-bded-3868e247a1ec
-- title:
--   Lemma 3.2 — cut barriers
-- statement:
--   Let $K$ be a reduced tree to which no good reconnection applies.
--
--   1. If $x,x'\in T$ and $e\in E_S(K)$ lies on the tree path between them, then $w(x,x')>\chi w(e)$. Consequently no component of $G_a(T)\cup E_T(K)$ has terminals on both sides of an edge $e\in E_S(K)$ with $\chi w(e)\ge a$.
--   2. In every cherry $s'<s/(\chi-1)$, and every limb has $W\le(1+\frac1{\chi-1})r$.
--   3. Every terminal pair with exactly one terminal in the region of a limb of length $r$ is at distance greater than
--   $$\chi z+(\chi-1)(s+s')\ge pr,$$
--   where $z=r$ and $s=s'=0$ for a direct limb. Hence, for $a\le pr$, no component of $G_a(T)\cup E_T(K)$ meets both the region and its complement.
--
--   These barriers are what place a star's ports in different exact components, and so tie the reduction process to the statistics $\Gamma$ and $\Lambda$.
--
--   Differences from the source:
--   - encoding: terminals on both sides of e; a component meeting the region and its complement → two terminals not connected in K − e; terminals in the region and outside it; reason: components of G_a(T) ∪ E_T(K) consist of terminals, so this is the same statement
--   - generalization: K the current tree of the reduction process of §3.1 (an optimal Steiner tree after good reconnections, events and cleanup) → any feasible tree on T whose nonterminals all have degree at least three (ReducedTree); reason: the proof uses only the tree structure and the absence of good reconnections; every state of the process after cleanup is such a tree
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 3.2, p.16

import Mathlib
import Definitions.Def_SublinearSteiner_ReducedTree

namespace SublinearSteiner

open ReducedTree in
/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 3.2 (Cut barriers), p.16. Suppose that no good reconnection applies.
(i) If `x, x′ ∈ T` and `e ∈ E_S(K)` lies on the tree path between them, then `w(x, x′) > χ w(e)`. Consequently no component
of `G_a(T) ∪ E_T(K)` has terminals on both sides of an edge `e ∈ E_S(K)` with `χ w(e) ≥ a`.
(ii) In every cherry `s′ < s/(χ − 1)`, and every limb has `W ≤ (1 + 1/(χ − 1)) r`.
(iii) Every terminal pair with exactly one terminal in the region of a limb of length `r` is at distance greater than
`χz + (χ − 1)(s + s′) ≥ pr`, where `z = r` and `s = s′ = 0` for a direct limb. Hence, for `a ≤ pr`, no component of
`G_a(T) ∪ E_T(K)` meets both the region and its complement.

**Formalization Note.** Two terminals are on the two sides of `e` when they are not connected in `K − e`. Components of
`G_a(T) ∪ E_T(K)` consist of terminals, so "the region and its complement" is read on `T`. -/
theorem lemma_3_2 {n : ℕ} (w : FinMetric n) (T : Finset (Fin n)) (K : ReducedTree T)
    (hK : K.NoGoodReconnection w) :
    ((∀ x ∈ T, ∀ x' ∈ T, ∀ e ∈ K.steinerEdges,
        (∃ p : (edgeGraph K.E).Walk x x', p.IsPath ∧ e ∈ p.edges) → chi * w.edgeLen e < w.d x x') ∧
      (∀ a : ℝ, 0 < a → ∀ e ∈ K.steinerEdges, a ≤ chi * w.edgeLen e → ∀ x ∈ T, ∀ x' ∈ T,
        (K.augGraph w a).Reachable x x' → (K.minusEdge e).Reachable x x')) ∧
    ((∀ v y x x' : Fin n, K.IsLimbAt w v (.cherry y x x') → w.d y x' < w.d y x / (chi - 1)) ∧
      (∀ (v : Fin n) (l : Limb n), K.IsLimbAt w v l →
        l.cost w v ≤ (1 + 1 / (chi - 1)) * l.length w v)) ∧
    (∀ (v : Fin n) (l : Limb n), K.IsLimbAt w v l →
      (∀ c ∈ T, c ∈ K.region v l → ∀ b ∈ T, b ∉ K.region v l →
        chi * l.trunk w v + (chi - 1) * (l.armS w + l.armL w) < w.d c b) ∧
      pConst * l.length w v ≤ chi * l.trunk w v + (chi - 1) * (l.armS w + l.armL w) ∧
      (∀ a : ℝ, 0 < a → a ≤ pConst * l.length w v → ∀ x ∈ T, x ∈ K.region v l → ∀ x' ∈ T,
        x' ∉ K.region v l → ¬ (K.augGraph w a).Reachable x x')) := by sorry

end SublinearSteiner
