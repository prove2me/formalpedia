-- Prove2me | Theorems.Thm_SLQSolv_MinSeq_lemma_6_3
-- name    : SLQSolv.MinSeq.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:08.907935+00:00
-- url     : https://prove2.me/theorems/dd09237d-17d6-4b66-8498-133a40afa7dd
-- title:
--   Lemma 6.3, p. 2301 — in a Hilbert space, ‖θ‖ ⩽ liminf ‖θₙ‖ under weak convergence; strong ⟺ weak + convergence of norms
-- statement:
--   Let $\mathcal H$ be a real Hilbert space with norm $\|\cdot\|$ and let $\theta,\theta_n\in\mathcal H$, $n=1,2,\dots$. Say $\theta_n\to\theta$ weakly if $\langle\theta_n,y\rangle\to\langle\theta,y\rangle$ for every $y\in\mathcal H$.
--
--   1. If $\theta_n\to\theta$ weakly, then $$\|\theta\|\le\liminf_{n\to\infty}\|\theta_n\|.$$
--   2. $\theta_n\to\theta$ strongly if and only if $\|\theta_n\|\to\|\theta\|$ and $\theta_n\to\theta$ weakly.
--
--   In the proof of Theorem 6.2 these facts upgrade a weakly convergent subsequence of $u_\varepsilon$ to a strongly convergent one.
--
--   **Formalization Note** The liminf in (1) is taken in $[0,\infty]$, so it is meaningful for unbounded sequences. Weak convergence is written through the inner product. The space is real; the paper's $\mathcal U[t,T]$ is a real Hilbert space.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Lemma 6.3, p. 2301

import Mathlib

open Filter Topology
open scoped ENNReal InnerProductSpace

namespace SLQSolv.MinSeq

/-- Lemma 6.3, p. 2301: in a real Hilbert space, (i) if `θₖ → θ` weakly then
`‖θ‖ ≤ liminf ‖θₖ‖` (in `[0, ∞]`); (ii) `θₖ → θ` strongly iff `‖θₖ‖ → ‖θ‖` and `θₖ → θ` weakly. -/
theorem lemma_6_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (θ : H) (θs : ℕ → H) :
    ((∀ y : H, Tendsto (fun k => ⟪θs k, y⟫_ℝ) atTop (𝓝 ⟪θ, y⟫_ℝ)) →
        ‖θ‖ₑ ≤ Filter.liminf (fun k => ‖θs k‖ₑ) atTop) ∧
      (Tendsto θs atTop (𝓝 θ) ↔
        Tendsto (fun k => ‖θs k‖) atTop (𝓝 ‖θ‖) ∧
          ∀ y : H, Tendsto (fun k => ⟪θs k, y⟫_ℝ) atTop (𝓝 ⟪θ, y⟫_ℝ)) := by sorry

end SLQSolv.MinSeq
