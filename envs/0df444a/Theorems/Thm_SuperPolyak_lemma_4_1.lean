-- Prove2me | Theorems.Thm_SuperPolyak_lemma_4_1
-- name    : SuperPolyak.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:12:47.983284+00:00
-- url     : https://prove2.me/theorems/b41a4e82-ebc7-4880-8309-16d04c97e889
-- title:
--   Lemma 4.1 — a nearest point of $X^*$ to $x\in B_{\delta'}(y)$ lies in $B_{2\delta'}(y)$
-- statement:
--   Let $X\subseteq\mathbb R^d$, let $\delta'>0$ and let $y\in X$. If $x\in B_{\delta'}(y)$ and $\hat x\in P_X(x)$ is a nearest point of $X$ to $x$, then
--   $$
--   \hat x\in B_{2\delta'}(y).
--   $$
--   In the paper $X=X^*$, the solution set; the lemma is what allows the $(b)$-regularity estimate (A2), which requires $y\in X^*\cap B_{2\delta}(\bar x)$, to be applied at nearest points $\hat x$.
--
--   **Formalization Note** Balls are open. $P_X(x)$ is the set of nearest points.
--
--   Differences from the source:
--
--   - generalization: X* = argmin f → an arbitrary set X ⊆ ℝᵈ; reason: the statement uses only y ∈ X and the nearest-point property of x̂; X = solutionSet f is the paper's lemma
-- source:
--   Charisopoulos & Davis, A superlinearly convergent subgradient method for sharp semismooth problems, arXiv:2201.04611v1, Lemma 4.1, p.22

import Mathlib
import Definitions.Def_SuperPolyak_solutionSet

namespace SuperPolyak

/-- **Lemma 4.1** (Charisopoulos & Davis, *A superlinearly convergent subgradient method for sharp
semismooth problems*, arXiv:2201.04611v1, Lemma 4.1, p.22). Let `δ' > 0` and `y ∈ X*`. If
`x ∈ B_{δ'}(y)` and `x̂ ∈ P_{X*}(x)`, then `x̂ ∈ B_{2δ'}(y)`.

**Formalization Note** Stated for an arbitrary set `X ⊆ ℝᵈ` in place of `X*` (the proof uses only
`y ∈ X` and the nearest-point property); taking `X = solutionSet f` gives the paper's lemma. Balls
are open. -/
theorem lemma_4_1 {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) {δ' : ℝ} (hδ' : 0 < δ')
    {y x xhat : EuclideanSpace ℝ (Fin d)} (hy : y ∈ X) (hx : x ∈ Metric.ball y δ')
    (hxhat : xhat ∈ nearestPoints X x) :
    xhat ∈ Metric.ball y (2 * δ') := by sorry

end SuperPolyak
