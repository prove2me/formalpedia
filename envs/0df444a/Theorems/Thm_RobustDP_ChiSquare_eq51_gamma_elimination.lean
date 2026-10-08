-- Prove2me | Theorems.Thm_RobustDP_ChiSquare_eq51_gamma_elimination
-- name    : RobustDP.ChiSquare.eq51_gamma_elimination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:06.260135+00:00
-- url     : https://prove2.me/theorems/169b76a0-c778-4bcc-89de-659ddf9e603c
-- title:
--   Proof of Lemma 5, eq. (51) — the optimal γ turns the sum of squares into $\mathrm{Var}^q[v-\mu]$
-- statement:
--   Let $\mathcal S$ be a finite set, $q\in\mathcal M(\mathcal S)$ with $q(s)>0$ for every $s$, $t\ge 0$ and $v,\mu:\mathcal S\to\mathbb R$. Then
--
--   $$
--   \max_{\gamma\in\mathbb R}\Big\{\mathbf E^q[v-\mu]-\sqrt{t\sum_{s}q(s)\big(v(s)-\mu(s)-\gamma\big)^2}\Big\}
--   =\mathbf E^q[v-\mu]-\sqrt{t\,\mathbf{Var}^q[v-\mu]},
--   $$
--
--   and the maximum is attained at $\gamma=\mathbf E^q[v-\mu]$.
--
--   Together with (50), this identifies the Lagrangian dual of (49) with the mean–standard-deviation problem (48).
--
--   **Formalization Note** The maximum is Mathlib's `IsGreatest` of the image of $\mathbb R$; the right-hand side is the dual objective $g_{q,t,v}(\mu)$ of the definitions item. As in (50), $\gamma$ ranges over all of $\mathbb R$.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 18, proof of Lemma 5, eq. (51)

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_ChiSqSet

namespace RobustDP.ChiSquare

/-- Proof of Lemma 5, eq. (51) (Iyengar, TR-2002-07, p. 18): maximizing
`E^q[v − μ] − √(t ∑ q(s)(v(s) − μ(s) − γ)²)` over `γ ∈ ℝ` gives `E^q[v − μ] − √(t Var^q[v − μ])`,
attained at `γ = E^q[v − μ]`. -/
theorem eq51_gamma_elimination {S : Type*} [Fintype S] (q : S → ℝ)
    (hq : q ∈ stdSimplex ℝ S) (hq_pos : ∀ s, 0 < q s) (t : ℝ) (ht : 0 ≤ t) (v μ : S → ℝ) :
    IsGreatest ((fun γ : ℝ => expect q (v - μ) - Real.sqrt (t * ∑ s, q s * (v s - μ s - γ) ^ 2)) ''
        Set.univ)
      (dualObj q t v μ) ∧
    expect q (v - μ) - Real.sqrt (t * ∑ s, q s * (v s - μ s - expect q (v - μ)) ^ 2) =
      dualObj q t v μ := by sorry

end RobustDP.ChiSquare
