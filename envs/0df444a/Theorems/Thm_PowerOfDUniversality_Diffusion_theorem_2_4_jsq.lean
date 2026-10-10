-- Prove2me | Theorems.Thm_PowerOfDUniversality_Diffusion_theorem_2_4_jsq
-- name    : PowerOfDUniversality.Diffusion.theorem_2_4_jsq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:35:43.020809+00:00
-- url     : https://prove2.me/theorems/d53ecb2b-2d6a-4a42-a2ed-ac1031d5cf61
-- title:
--   Theorem 2.4 for $d(N)=N$ — the Halfin–Whitt diffusion limit of the ordinary JSQ policy ([8, Theorem 2])
-- statement:
--   Let $\beta>0$, let the buffer size be $b\ge2$ (possibly infinite), let $k\ge2$, and let $\nu$ be a probability measure on $\mathbb R^k$. Consider any sequence of systems under the ordinary join-the-shortest-queue policy, the $j$-th with $N_j$ servers and arrival rate $\lambda_j$, where $N_j\to\infty$ and
--   $$\frac{N_j-\lambda_j}{\sqrt{N_j}}\to\beta .$$
--   Assume that $Q_{k+1}(0)=0$ almost surely for all large $j$, and that $(\bar Q_1(0),\dots,\bar Q_k(0))$ converges in distribution to $\nu$. Then the diffusion-scaled occupancy processes $\bar Q^{N_j}$ converge weakly in $D_{\ell_1}[0,\infty)$ to a limit $\bar Q$ with $\bar Q_i\equiv0$ for $i\ge k+1$. The first $k$ coordinates of $\bar Q$, together with a regulator $U_1$, solve (2.4) driven by a standard Brownian motion $W$, from an initial value with law $\nu$ independent of $W$.
--
--   The paper does not reprove this case: "This diffusion limit is proved in [8] for the ordinary JSQ policy" (p. 8), and "the diffusion limit for the ordinary JSQ policy is obtained in [8, Theorem 2], and characterized by (2.4)" (p. 32). It is the starting point of the proof of Theorem 2.4.
--
--   **Formalization Note** This is Theorem 2.4 in the case $d(N)=N$ (ordinary JSQ), which the paper attributes to [8, Theorem 2]. JSQ is the JSQ(d) system with every server sampled. The statement is made for an arbitrary sequence of server counts $N_j\to\infty$ rather than $N=1,2,\dots$, because the proof of Proposition 5.1 applies it to $\bar N=N-n(N)$ servers. Only the existence-and-convergence half of Theorem 2.4 is stated here; uniqueness is a separate milestone.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 7–8, Theorem 2.4 with d(N) = N; attributed to Eschenfeldt & Gamarnik [8, Theorem 2] on pp. 8 and 32

import Mathlib
import Definitions.Def_PowerOfDUniversality_Diffusion_HalfinWhitt

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Diffusion

/-- **Theorem 2.4 in the case `d(N) = N`: the diffusion limit of the ordinary JSQ policy**
(Mukherjee, Borst, van Leeuwaarden & Whiting, arXiv:1612.00723v2, pp. 7–8; attributed to
[8, Theorem 2] on pp. 8 and 32). Let `β > 0`, `b ≥ 2` (possibly `⊤`), `k ≥ 2` and let `ν` be a
probability measure on `ℝ^k`. Take any sequence of JSQ systems (every server sampled, `d = Ns`)
with server counts `Ns j → ∞`, arrival rates `lam j` in the Halfin–Whitt regime
`(Ns j − lam j)/√(Ns j) → β`, initial states with `Q_{k+1}(0) = 0` eventually and diffusion-scaled
initial values converging jointly in law to `ν` (`IsHWSequence`). Then the diffusion-scaled
occupancy processes converge weakly in `D_{ℓ¹}[0, ∞)` to a limit that solves (2.4) driven by a
standard Brownian motion from an independent initial value with law `ν` (`HasDiffusionLimit24`). -/
theorem theorem_2_4_jsq (β : ℝ) (hβ : 0 < β) (b : ℕ∞) (hb : 2 ≤ b) (k : ℕ) (hk : 2 ≤ k)
    (ν : Measure (Fin k → ℝ)) (Ns : ℕ → ℕ) (lam : ℕ → ℝ) {Ω : ℕ → Type}
    [∀ j, MeasurableSpace (Ω j)] (P : ∀ j, Measure (Ω j)) (Q₀ : ∀ j, Ω j → ℕ → ℕ)
    (E : ∀ j, Ω j → ℕ → ℝ) (M : ∀ j, Ω j → ℕ → Mark)
    (hseq : IsHWSequence β b k ν Ns Ns lam P Q₀ E M) :
    HasDiffusionLimit24 β k ν P
      (fun j ω => diffusionProcess b (Ns j) (Q₀ j ω) (E j ω) (M j ω)) := by sorry

end PowerOfDUniversality.Diffusion
