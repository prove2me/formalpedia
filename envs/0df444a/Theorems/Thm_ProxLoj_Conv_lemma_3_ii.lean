-- Prove2me | Theorems.Thm_ProxLoj_Conv_lemma_3_ii
-- name    : ProxLoj.Conv.lemma_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:24.915082+00:00
-- url     : https://prove2.me/theorems/94acbaa8-3ef1-4276-bce3-d797f3b5cbfb
-- title:
--   Lemma 3 (ii), p. 4 — the uniform Łojasiewicz inequality (6) near a compact connected set of critical points
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be proper, lower semicontinuous, continuous on its domain (H2), with the Łojasiewicz property (H3). Let $K\subset\operatorname{crit} f$ be connected and compact. Then there exist $C,\varepsilon>0$ and $\theta\in[0,1)$ such that, for every $\hat x\in K$,
--   $$|f(x)-f(\hat x)|^\theta\le C|x^*|\qquad\forall x\in\mathbb R^n \text{ with } d(x,K)\le\varepsilon,\ \forall x^*\in\partial f(x),\qquad(6)$$
--   with the convention $0^0=0$.
--
--   The local inequalities (5) at the points of $K$ become one inequality with common constants on a uniform neighbourhood of $K$. This is the form in which the Łojasiewicz property enters the convergence proof, with $K=\omega(x^0)$.
--
--   **Formalization Note** On the page $\hat x$ in (6) is not bound; by (i) $f$ is constant on $K$, so $f(\hat x)$ is that common value, and the statement quantifies over $\hat x\in K$. For $K=\emptyset$ the statement is vacuous, which avoids the junk value $d(x,\emptyset)=0$. The values $f(x)$, $f(\hat x)$ are finite where they are used ($x^*\in\partial f(x)$ forces $f(x)<+\infty$; $\hat x$ is critical) and are converted to reals.
-- source:
--   Attouch & Bolte, On the convergence of the proximal algorithm for nonsmooth functions involving analytic features, author's version hal-00803898v1, p. 4, Lemma 3 (ii), display (6)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
import Definitions.Def_ProxLoj_Conv_Setting

open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous

namespace ProxLoj.Conv

/-- Lemma 3 (ii), p. 4, display (6): if moreover `K` is compact, there are `C, ε > 0` and
`θ ∈ [0, 1)` with `|f(x) - f(x̂)|^θ ≤ C ‖x*‖` for every `x` with `d(x, K) ≤ ε`, every
`x* ∈ ∂f(x)`, and `x̂ ∈ K` (the common value of `f` on `K`). -/
theorem lemma_3_ii {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hproper : IsProper f)
    (hlsc : LowerSemicontinuous f) (hH2 : H2 f) (hH3 : HasLojProperty f)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : K ⊆ crit f) (hconn : IsPreconnected K)
    (hcpt : IsCompact K) :
    ∃ C ε θ : ℝ, 0 < C ∧ 0 < ε ∧ 0 ≤ θ ∧ θ < 1 ∧
      ∀ xh ∈ K, ∀ x, Metric.infDist x K ≤ ε → ∀ v ∈ LimitingSubdiff f x,
        lojPow θ |(f x).toReal - (f xh).toReal| ≤ C * ‖v‖ := by sorry

end ProxLoj.Conv
