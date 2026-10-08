-- Prove2me | Theorems.Thm_SelfishRouting_Linear_lemma_4_3_b
-- name    : SelfishRouting.Linear.lemma_4_3_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:49.684437+00:00
-- url     : https://prove2.me/theorems/80e27412-7fba-4c48-9483-4271c4153299
-- title:
--   Lemma 4.3(b) — the marginal cost of a path w.r.t. $f/2$ equals its latency w.r.t. $f$: $\ell^*_P(f/2)=\ell_P(f)$
-- statement:
--   Let every edge have a linear latency $\ell_e(x)=a_ex+b_e$, with marginal cost $\ell^*_e(x)=2a_ex+b_e$. For every route flow $f$ and every route $P$, the marginal cost of increasing the flow on $P$ with respect to $f/2$ equals the latency of $P$ with respect to $f$:
--   $$\ell^*_P(f/2)=\sum_{e\in P}\ell^*_e(f_e/2)=\sum_{e\in P}\ell_e(f_e)=\ell_P(f).$$
--
--   It connects the marginal costs at the optimal flow $f/2$ of Lemma 4.3(a) with the equilibrium latencies of $f$, and through Lemma 2.3 with the cost $C(f)$.
--
--   **Formalization Note** The page states (b) under the lemma's preamble ("$f$ is a flow at Nash equilibrium"). The identity holds edge by edge for every flow, so the formal statement drops the equilibrium hypothesis (and the sign conditions on $a_e,b_e$ and the incidence); it is the stronger identity and implies the page's statement.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 15, Lemma 4.3(b)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

namespace SelfishRouting.Linear

/-- Lemma 4.3(b) (p. 15): with linear latencies, the marginal cost `ℓ*_P(f/2)` of every route
with respect to `f/2` equals its latency `ℓ_P(f)` with respect to `f`. Stated for every flow
`f` (the page's equilibrium hypothesis is not needed). -/
theorem lemma_4_3_b {J R : ℕ} (A : Fin J → Fin R → ℝ) (a b : Fin J → ℝ)
    (x : Fin R → ℝ) (r : Fin R) :
    SelfishRouting.Bicriteria.pathLatency A (marginalLatency a b) (fun r => x r / 2) r =
      SelfishRouting.Bicriteria.pathLatency A (linLatency a b) x r := by sorry

end SelfishRouting.Linear
