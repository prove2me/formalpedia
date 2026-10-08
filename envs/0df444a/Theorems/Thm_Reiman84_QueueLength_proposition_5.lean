-- Prove2me | Theorems.Thm_Reiman84_QueueLength_proposition_5
-- name    : Reiman84.QueueLength.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:06:54.634019+00:00
-- url     : https://prove2.me/theorems/755ffe80-c71b-4fda-8ecb-b8966f982fd3
-- title:
--   Proposition 5 — ζ̃ⁿ ⇒ ζ
-- statement:
--   Consider a sequence of networks of §2 satisfying (20)–(26), let $(Q^n,B^n)$ solve (1)–(3) almost surely, let $\tilde X^n$ be the centred process (10) built with $B^n$, and $\tilde\zeta^n(t)=n^{-1/2}\tilde X^n(nt)$, $0\le t\le1$. If $\zeta$ is a $K$-dimensional Brownian motion with drift $c$ and covariance $\mathcal A$ of (27)–(28), then
--   $$\tilde\zeta^n\Rightarrow\zeta\quad\text{in } D\text{ as } n\to\infty.$$
--
--   Together with $Z^n=f(\tilde\zeta^n)$ and Proposition 2, this yields Theorem 1 by the continuous mapping theorem.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), p. 451, Proposition 5

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

namespace Reiman84.QueueLength

open Filter Topology MeasureTheory

/-- Proposition 5, p. 451: under (20)–(26), `ζ̃ⁿ ⇒ ζ` in `D`, where `ζ̃ⁿ(t) = n^{-1/2} X̃ⁿ(nt)`
and `ζ` is a `K`-dimensional Brownian motion with drift `c` and covariance `𝒜`. -/
theorem proposition_5 {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ)
    (hQ : ∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (ζ : Ω' → ℝ → Fin K → ℝ)
    (hζ : IsDriftedBM c (covA lam a mu s R) P' ζ) :
    WeakConvD P (fun n ω => diffScale n (fun t => (net n).Xtilde (B n ω) t ω)) P' ζ := by sorry

end Reiman84.QueueLength
