-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_interleaving_corrected
-- name    : PersistClust.Count.theorem_4_5_interleaving_corrected
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-09T11:29:20.76999+00:00
-- url     : https://prove2.me/theorems/765c1ed6-f4cf-4784-b544-628642d8922a
-- title:
--   Geometric interleaving (corrected): superlevel and Rips filtrations are cδ-interleaved above α in box-expansion rank form
-- statement:
--   This is the corrected form of the geometric ingredient in the proof of Theorem 4.5 (p. 21), which adapts the proof of Theorem 4.4 of [6, §3.1].
--
--   Let $X$ be a Riemannian manifold of positive convexity radius, $f : X \to \mathbb R$ tame (`IsTame0`) and $c$-Lipschitz, and $L$ a finite geodesic $(\delta/4)$-sample of the superlevel set $F^\alpha = f^{-1}([\alpha,\infty))$, with $0 < \delta$ below the convexity radius. Then the superlevel-set filtration $\{F^\beta\}$ of $f$ and the upper-star Rips filtration $\{\mathcal R^f_\delta(L^\beta)\}$ of the sample are both genuine 0-dimensional persistence filtrations (their stage families decrease and their join relations are the component equivalences — the `FiltrationLaw` conjuncts), their 0-th persistence diagrams are diagram-like with finite off-diagonal support, and the two filtrations are strongly $c\delta$-interleaved above $\alpha$. In rank form this yields the box-expansion inequalities: for all $s \ge t + 2c\delta$ with $t \ge \alpha$,
--   $$ \operatorname{superRank} f(s,t) \le \operatorname{ripsRank}_\delta(s-c\delta,\,t+c\delta), \qquad \operatorname{ripsRank}_\delta(s,t) \le \operatorname{superRank} f(s-c\delta,\,t+c\delta), $$
--   where $\operatorname{superRank} f(s,t)$ is the number of path components of $F^t$ meeting $F^s$ and $\operatorname{ripsRank}_\delta(s,t)$ is the number of connected components of the Rips graph $R_\delta(L^t)$ meeting $L^s$.
--
--   This is the reusable geometric lemma for Theorem 4.5; its conclusion is exactly the hypothesis set of the corrected algebraic child, with $r_X = \operatorname{superRank} f$, $r_Y = \operatorname{ripsRank}_\delta$ and $\varepsilon = c\delta$.
--
--   **Formalization Note.** The inequalities are asserted only in the box $s \ge t + 2c\delta$, $t \ge \alpha$, the region where the interleaving maps factor and hence genuinely constrain the ranks. The naive shift $r(s,t) \le r'(s-\varepsilon, t-\varepsilon)$, quantified over all $t \le s$ with $s \ge \alpha$, is falsified at $s = t = \alpha$ by elementary examples on $X = \mathbb R$ (it probes ranks below the sampled level $\alpha$); the box-expansion form avoids this.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968, 2009, pp. 20–21, Theorem 4.5 (proof via Theorem 4.4 of Chazal–Oudot, Geometric Inference for Probability Measures, [6, §3.1]); https://hal.inria.fr/inria-00389352

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_FiltrationLaw
open Bundle
open scoped ContDiff Manifold

namespace PersistClust.Count

theorem theorem_4_5_interleaving_corrected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X]
    (hconv : 0 < convexityRadius X)
    (L : Finset X) (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (htame : IsTame0 f)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (α : ℝ) (hL : IsGeodesicSample (L : Set X) (superlevel f α) (δ / 4)) :
    FiltrationLaw (superlevel f) (fun t => JoinedIn (superlevel f t)) ∧
    FiltrationLaw (fun t => {i | t ≤ (fun x : L => f x) i})
      (ripsJoined (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ) ∧
    IsDiagramLike (diagram0 f) ∧
    IsDiagramLike (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ) ∧
    {p : EReal × EReal | (diagram0 f) p ≠ 0}.Finite ∧
    {p : EReal × EReal |
        (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ) p ≠ 0}.Finite ∧
    (∀ s t : ℝ, t + 2 * (c * δ) ≤ s → α ≤ t →
       superRank f s t ≤
         ripsRank (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ (s - c * δ) (t + c * δ) ∧
       ripsRank (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ s t ≤
         superRank f (s - c * δ) (t + c * δ)) := by sorry

end PersistClust.Count
