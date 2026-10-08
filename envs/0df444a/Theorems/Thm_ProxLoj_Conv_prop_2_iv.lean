-- Prove2me | Theorems.Thm_ProxLoj_Conv_prop_2_iv
-- name    : ProxLoj.Conv.prop_2_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:38.933445+00:00
-- url     : https://prove2.me/theorems/1b809f8f-8b32-40af-810d-24c41cedcf0e
-- title:
--   Proposition 2 (iv), p. 3 — for a bounded proximal run, ω(x⁰) is nonempty, compact, connected and d(x^k, ω(x⁰)) → 0
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be proper with $\inf f>-\infty$ (H1), let $0<\lambda_-<\lambda_+$, $\lambda_k\in(\lambda_-,\lambda_+)$, and let $(x^k)$ comply with (2). If $(x^k)$ is bounded, then its set of limit points $\omega(x^0)$ is a nonempty, compact, connected subset of $\mathbb R^n$, and
--   $$d\big(x^k,\omega(x^0)\big)\to0\qquad(k\to+\infty).$$
--
--   This is the topological part of Proposition 2; together with (iii) it makes $\omega(x^0)$ a compact connected set of critical points, the set $K$ to which Lemma 3 is applied.
--
--   **Formalization Note** Lower semicontinuity and (H2)–(H3) are not needed and are dropped. $d(x,S)$ is `Metric.infDist`; nonemptiness is part of the conclusion, so the junk value $d(x,\emptyset)=0$ plays no role.
-- source:
--   Attouch & Bolte, On the convergence of the proximal algorithm for nonsmooth functions involving analytic features, author's version hal-00803898v1, p. 3, Proposition 2 (iv)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
import Definitions.Def_ProxLoj_Conv_Setting

open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous

namespace ProxLoj.Conv

/-- Proposition 2 (iv), p. 3: for a bounded proximal run, `ω(x⁰)` is nonempty, compact and
connected, and `d(x^k, ω(x⁰)) → 0`. -/
theorem prop_2_iv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hproper : IsProper f)
    (hH1 : H1 f) (lam : ℕ → ℝ) (lamMinus lamPlus : ℝ) (hstep : StepBounds lam lamMinus lamPlus)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsProxRun f lam x)
    (hbdd : Bornology.IsBounded (Set.range x)) :
    (limitSet x).Nonempty ∧ IsCompact (limitSet x) ∧ IsConnected (limitSet x) ∧
      Tendsto (fun k => Metric.infDist (x k) (limitSet x)) atTop (𝓝 0) := by sorry

end ProxLoj.Conv
