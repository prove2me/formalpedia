-- Prove2me | Theorems.Thm_WeakMFG_Existence_proposition_7_4
-- name    : WeakMFG.Existence.proposition_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:28.672664+00:00
-- url     : https://prove2.me/theorems/1ff2cf48-6c69-468d-aa1c-aead7e192cd3
-- title:
--   Proposition 7.4 — a Kakutani-type fixed point x ∈ φ(x, Γ(x)) (corrected: nonempty compact convex values)
-- statement:
--   Let $K$ be a nonempty compact convex metrizable subset of a locally convex topological vector space and let $E$ be a normed vector space. Let $\Gamma:K\to2^E$ be upper hemicontinuous with nonempty, compact and convex values, and let $\phi:K\times E\to K$ be continuous. Then there is $x\in K$ such that
--   $$x\in\phi(x,\Gamma(x)):=\{\phi(x,y):y\in\Gamma(x)\}.$$
--
--   This generalization of Kakutani's theorem is the fixed point theorem behind the existence of a mean field game solution.
--
--   **Formalization Note** The page assumes *closed* convex values and does not ask that they be nonempty. As printed the statement is false: $\Gamma\equiv\emptyset$ is a counterexample, and so is the following one with nonempty closed values. Take $K=[0,1]$ and $E=\mathbb R^2$. Let $\Gamma(x)=\{(0,0)\}$ for $x<\tfrac12$, $\Gamma(x)=\{(1,(x-\tfrac12)^{-1})\}$ for $x>\tfrac12$, and $\Gamma(\tfrac12)=\{0\le y_1\le1,\ y_2\ge2y_1\}$. Let $\phi(x,y)=\mathrm{clamp}_{[0,1]}\big(x+\tfrac14-\tfrac12\,\mathrm{clamp}_{[0,1]}(y_2(x-\tfrac12))\big)$. Then $\Gamma$ is upper hemicontinuous with closed convex values, but $\phi(x,y)\neq x$ whenever $y\in\Gamma(x)$. The page's proof uses that $\Gamma(K)$ is compact (Aliprantis–Border Lemma 17.8, which needs compact values) and Cellina's approximate-selection theorem (which needs nonempty values). Those are the hypotheses stated here.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Proposition 7.4, p. 23

import Mathlib
import Definitions.Def_WeakMFG_Existence_UHC

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

/-- Proposition 7.4 (Carmona–Lacker, arXiv:1307.1152v2, p. 23), corrected: let `K` be a nonempty
compact convex metrizable subset of a locally convex topological vector space and `E` a normed
vector space. Suppose `Γ : K → 2^E` is upper hemicontinuous with nonempty, compact and convex
values, and `φ : K × E → K` is continuous. Then there is `x ∈ K` with
`x ∈ φ(x, Γ(x)) := {φ(x, y) : y ∈ Γ(x)}`.
Formalization Note: the page assumes closed (not compact) values and does not say nonempty. As
printed the statement is false (constant `Γ ≡ ∅`; and, with nonempty closed unbounded values, a
counterexample with `K = [0, 1]`, `E = ℝ²` recorded in the mission notes). The proof on the page
uses that `Γ(K)` is compact (A–B Lemma 17.8, which needs compact values) and Cellina's theorem
(nonempty values): those are the hypotheses stated here. -/
theorem proposition_7_4 {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set V) (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (hKm : TopologicalSpace.MetrizableSpace K) (hKne : K.Nonempty)
    (Γ : K → Set E) (hΓ : ∀ x, UHCAt Γ x) (hΓc : ∀ x, IsCompact (Γ x))
    (hΓconv : ∀ x, Convex ℝ (Γ x)) (hΓne : ∀ x, (Γ x).Nonempty)
    (φ : K × E → K) (hφ : Continuous φ) :
    ∃ x : K, ∃ y ∈ Γ x, φ (x, y) = x := by sorry

end WeakMFG.Existence
