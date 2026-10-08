-- Prove2me | Theorems.Thm_ProxLoj_Conv_lemma_3_i
-- name    : ProxLoj.Conv.lemma_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:25.651855+00:00
-- url     : https://prove2.me/theorems/637dc80e-00e0-4b1d-aea9-adad902747a3
-- title:
--   Lemma 3 (i), p. 4 — under the Łojasiewicz property, f is constant on every connected set of critical points
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be proper, lower semicontinuous, continuous on its domain (H2), and have the Łojasiewicz property (H3): at every critical point $\hat x$ there are $C,\varepsilon>0$ and $\theta\in[0,1)$ with $|f(x)-f(\hat x)|^\theta\le C|x^*|$ for all $x\in B(\hat x,\varepsilon)$ and $x^*\in\partial f(x)$ (with $0^0=0$). If $K$ is a connected subset of $\operatorname{crit} f$, then $f$ is constant on $K$:
--   $$f(y)=f(z)\qquad\text{for all } y,z\in K.$$
--
--   This rules out a continuum of critical values along a connected critical set, which is what lets the limit set of a bounded proximal sequence carry a single value of $f$.
--
--   **Formalization Note** Connectedness is `IsPreconnected`, which also admits $K=\emptyset$, where the claim is trivially true.
-- source:
--   Attouch & Bolte, On the convergence of the proximal algorithm for nonsmooth functions involving analytic features, author's version hal-00803898v1, p. 4, Lemma 3 (i)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
import Definitions.Def_ProxLoj_Conv_Setting

open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous

namespace ProxLoj.Conv

/-- Lemma 3 (i), p. 4: if `f` has the Łojasiewicz property and `K ⊆ crit f` is connected,
then `f` is constant on `K`. -/
theorem lemma_3_i {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hproper : IsProper f)
    (hlsc : LowerSemicontinuous f) (hH2 : H2 f) (hH3 : HasLojProperty f)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : K ⊆ crit f) (hconn : IsPreconnected K) :
    ∀ y ∈ K, ∀ z ∈ K, f y = f z := by sorry

end ProxLoj.Conv
