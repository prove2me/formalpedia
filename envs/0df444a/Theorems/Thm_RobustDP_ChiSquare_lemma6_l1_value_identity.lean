-- Prove2me | Theorems.Thm_RobustDP_ChiSquare_lemma6_l1_value_identity
-- name    : RobustDP.ChiSquare.lemma6_l1_value_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:01.170209+00:00
-- url     : https://prove2.me/theorems/88f79317-4bbf-4411-a154-b0176946a6fd
-- title:
--   Lemma 6 (as established in its proof, p. 20) — worst-case expectation over the $L_1$ ball
-- statement:
--   Let $\mathcal S$ be a finite set, $q\in\mathcal M(\mathcal S)$, $t\ge 0$, $c=\sqrt{2\ln(2)\,t}$ and $v:\mathcal S\to\mathbb R$. Then the problem
--
--   $$
--   \text{minimize } \mathbf E^p[v]\quad\text{subject to } p\in\mathcal M(\mathcal S),\ \|p-q\|_1\le c
--   $$
--
--   has an optimal solution, and its optimal value equals
--
--   $$
--   \max_{\mu\ge 0}\Big\{\mathbf E^q[v-\mu]-\tfrac12\,c\,\Big(\max_{s}\{v(s)-\mu(s)\}-\min_{s}\{v(s)-\mu(s)\}\Big)\Big\},
--   $$
--
--   the maximum being over $\mu:\mathcal S\to\mathbb R$ with $\mu\ge 0$, and attained.
--
--   This is the $L_1$ analogue of Lemma 5: the worst case over an outer approximation of the relative-entropy region is again a one-dimensional dual problem.
--
--   **Formalization Note** This is the identity the proof of Lemma 6 establishes (its last display), not the printed formula (57), which is false: in (57), $\mu=v-\min_s v(s)\ge 0$ makes the bracket $0$, so (57) always equals $\mathbf E^q[v]$; for $\mathcal S=\{1,2\}$, $q=(\tfrac12,\tfrac12)$, $v=(0,1)$ and $c=\tfrac12$ the true minimum is $\tfrac14$, not $\tfrac12$. The set is restricted to $p\in\mathcal M(\mathcal S)$, which (55)–(56) omit but the proof uses. The complexity claim of Lemma 6 is not formalized. Maxima and minima over $\mathcal S$ are `⨆`/`⨅` over a finite nonempty type.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 20, Lemma 6, (56), last display of the proof

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_L1Set

namespace RobustDP.ChiSquare

/-- Lemma 6 as established in its proof (Iyengar, TR-2002-07, p. 20, last display of the proof),
not the printed (57), which is false. For `q ∈ M(S)`, `t ≥ 0` and `c = √(2 ln(2) t)`, the minimum
of `Eᵖ[v]` over `{p ∈ M(S) : ‖p − q‖₁ ≤ c}` equals the maximum over `μ ≥ 0` of
`E^q[v − μ] − ½ c (max_s (v(s) − μ(s)) − min_s (v(s) − μ(s)))`. -/
theorem lemma6_l1_value_identity {S : Type*} [Fintype S] (q : S → ℝ)
    (hq : q ∈ stdSimplex ℝ S) (t : ℝ) (ht : 0 ≤ t) (v : S → ℝ) :
    ∃ val : ℝ,
      IsLeast ((fun p => expect p v) '' l1Set q (Real.sqrt (2 * Real.log 2 * t))) val ∧
      IsGreatest ((fun μ : S → ℝ => expect q (v - μ) -
          1 / 2 * Real.sqrt (2 * Real.log 2 * t) *
            ((⨆ s, (v s - μ s)) - ⨅ s, (v s - μ s))) '' {μ : S → ℝ | 0 ≤ μ}) val := by sorry

end RobustDP.ChiSquare
