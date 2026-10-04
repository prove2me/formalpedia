-- Prove2me | Theorems.Thm_StochApproxDyn_LimitSet_isAsymptoticPseudotrajectory_iff_tendsto_retraction
-- name    : StochApproxDyn.LimitSet.isAsymptoticPseudotrajectory_iff_tendsto_retraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:02:58.565794+00:00
-- url     : https://prove2.me/theorems/9613a809-b7c4-4abf-9cd6-8ed77f684405
-- title:
--   Lemma 3.1 — $X$ is an asymptotic pseudotrajectory iff $d(\Theta^t(X),\hat\Phi\circ\Theta^t(X))\to0$
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $(M,d)$, and use the translation semiflow $\Theta$, the retraction $\hat\Phi(Y)=\Phi^{Y(0)}$ and the distance $d$ on $C^0(\mathbb R_+,M)$. A continuous function $X:\mathbb R_+\to M$ is an asymptotic pseudotrajectory of $\Phi$ if and only if
--   $$\lim_{t\to\infty} d\big(\Theta^t(X),\hat\Phi\circ\Theta^t(X)\big)=0 .$$
--
--   In words: $X$ is an asymptotic pseudotrajectory exactly when its forward orbit under the translation semiflow is attracted by the set $S_\Phi$ of genuine trajectories.
--
--   **Formalization Note** Stated on $C^0(\mathbb R_+,M)$ (Mathlib's `C(ℝ≥0, M)`) with $d_k(f,g)=\sup_{s\in[0,k]}d(f(s),g(s))$. The source's version on $C^0(\mathbb R,M)$, with the extension $\Phi^p(t)=p$ for $t<0$, is false for semiflows (a periodic trajectory is a counterexample); the half-line version is the one the source's surrounding text describes.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 10, Lemma 3.1 (read on C⁰(ℝ₊, M))

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_TranslationSemiflow

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Lemma 3.1 (Benaïm 1999, p. 10), on `C⁰(ℝ₊, M)`: a continuous `X : ℝ₊ → M` is an asymptotic
pseudotrajectory of `Φ` iff `d(Θ^t(X), Φ̂(Θ^t(X))) → 0` as `t → ∞`. -/
theorem isAsymptoticPseudotrajectory_iff_tendsto_retraction {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (X : C(ℝ≥0, M)) :
    IsAsymptoticPseudotrajectory Φ X ↔
      Filter.Tendsto
        (fun t : ℝ≥0 => uniformCompactDist (translate t X) (retraction Φ (translate t X)))
        Filter.atTop (nhds 0) := by sorry

end StochApproxDyn.LimitSet
