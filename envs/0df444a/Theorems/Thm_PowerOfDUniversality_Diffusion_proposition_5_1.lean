-- Prove2me | Theorems.Thm_PowerOfDUniversality_Diffusion_proposition_5_1
-- name    : PowerOfDUniversality.Diffusion.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:35:34.628194+00:00
-- url     : https://prove2.me/theorems/78560a66-6dbd-455d-802d-7db716319e66
-- title:
--   Proposition 5.1 — if $d(N)/(\sqrt N\log N)\to\infty$, JSQ(d(N)) and JSQ have the same diffusion limit
-- statement:
--   Let $\beta>0$, $b\ge2$ (possibly infinite), $k\ge2$, and let $\nu$ be a probability measure on $\mathbb R^k$. Suppose the ordinary JSQ policy has the diffusion limit (2.4): along every Halfin–Whitt sequence of JSQ systems with parameters $\beta,b,k,\nu$ and any server counts $N_j\to\infty$, the diffusion-scaled occupancy processes converge weakly to the solution of (2.4). Consider a sequence of JSQ(d(N)) systems with $N=1,2,\dots$ servers that is a Halfin–Whitt sequence with these parameters, so that $(N-\lambda(N))/\sqrt N\to\beta$, $Q^N_{k+1}(0)=0$ for large $N$, and the initial values converge in law to $\nu$. If
--   $$\frac{d(N)}{\sqrt N\,\log N}\to\infty,$$
--   then the diffusion-scaled processes $\bar Q^{d(N)}$ also converge weakly in $D_{\ell_1}[0,\infty)$ to the solution of (2.4) driven by a standard Brownian motion from an independent initial value with law $\nu$.
--
--   This is the universality step of §5: together with the JSQ diffusion limit of [8, Theorem 2] it gives the convergence part of Theorem 2.4.
--
--   **Formalization Note** "The JSQ(d(N)) scheme and the ordinary JSQ policy have the same diffusion limit" is rendered as the paper's own reduction (p. 32): "the diffusion limit for the ordinary JSQ policy is obtained in [8, Theorem 2] … Therefore it suffices to prove the universality property". The JSQ result is the hypothesis, quantified over all sequences of server counts, because step (i) of the proof applies it to $\bar N=N-n(N)$ servers with $n(N)=N\log N/d(N)$. The consequent asserts convergence, not merely that limit points solve (2.4).
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 32, Proposition 5.1 (and the reduction stated before it)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Diffusion_HalfinWhitt

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Diffusion

/-- **Proposition 5.1** (Mukherjee, Borst, van Leeuwaarden & Whiting, arXiv:1612.00723v2, p. 32):
if `d(N)/(√N log N) → ∞`, the JSQ(d(N)) scheme and the ordinary JSQ policy have the same
diffusion limit. Rendered as the paper's reduction: fix `β > 0`, `b ≥ 2`, `k ≥ 2` and `ν`. If the
ordinary JSQ policy has the diffusion limit (2.4) along every Halfin–Whitt sequence of server
counts with these parameters (`JSQDiffusionLimitStatement β b k ν`), then every Halfin–Whitt
sequence of JSQ(d(N)) systems with `N = 1, 2, …` servers (`Ns = id`) and
`d(N)/(√N log N) → ∞` has the same diffusion limit (`HasDiffusionLimit24`). -/
theorem proposition_5_1 (β : ℝ) (hβ : 0 < β) (b : ℕ∞) (hb : 2 ≤ b) (k : ℕ) (hk : 2 ≤ k)
    (ν : Measure (Fin k → ℝ)) (hJSQ : JSQDiffusionLimitStatement β b k ν)
    (d : ℕ → ℕ) (lam : ℕ → ℝ) {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
    (P : ∀ N, Measure (Ω N)) (Q₀ : ∀ N, Ω N → ℕ → ℕ) (E : ∀ N, Ω N → ℕ → ℝ)
    (M : ∀ N, Ω N → ℕ → Mark)
    (hseq : IsHWSequence β b k ν (fun N => N) d lam P Q₀ E M)
    (hd : Tendsto (fun N : ℕ => (d N : ℝ) / (Real.sqrt N * Real.log N)) atTop atTop) :
    HasDiffusionLimit24 β k ν P
      (fun N ω => diffusionProcess b N (Q₀ N ω) (E N ω) (M N ω)) := by sorry

end PowerOfDUniversality.Diffusion
