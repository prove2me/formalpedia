-- Prove2me | Theorems.Thm_Reiman84_QueueLength_queue_length_heavy_traffic_limit
-- name    : Reiman84.QueueLength.queue_length_heavy_traffic_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:06:56.488977+00:00
-- url     : https://prove2.me/theorems/a76e29e9-025d-4e08-84fd-42387e2911f6
-- title:
--   Theorem 1 — the normalized queue-length process converges to reflected Brownian motion
-- statement:
--   Consider a sequence of open queueing networks of §2, indexed by $n\ge1$, each on its own probability space, with the same number $K$ of stations, the same set $\mathcal J$ of stations with exogenous arrivals and the same routing matrix $P$ (spectral radius $<1$), satisfying the heavy-traffic conditions (20)–(26) with limits $\mu,s,\lambda,a,c$. Let $(Q^n,B^n)$ solve (1)–(3) for the $n$th network, and let
--   $$Z^n(t)=n^{-1/2}Q^n(nt),\qquad 0\le t\le1.$$
--   Let $\xi$ be a $K$-dimensional Brownian motion with drift $c$, covariance matrix $\mathcal A$ of (27)–(28) and $\xi(0)=0$, and let $Z=\phi(\xi)$, with $\phi$ the reflection mapping of Lemma 1: $Z$ is a reflected Brownian motion on $\mathbb R^K_+$ with drift $c$, covariance $\mathcal A$ and reflection matrix $I-P$. Then
--   $$Z^n\Rightarrow Z\quad\text{in } D\text{ as } n\to\infty.$$
--
--   This is the heavy-traffic diffusion limit for open networks of single-server stations with general (GI) interarrival and service distributions and Markovian routing; it justifies approximating the queue-length vector of a heavily loaded network by a reflected Brownian motion.
--
--   **Formalization Note** $(Q^n,B^n)$ is any pair solving (1)–(3) almost surely (the solution exists and is unique, Section 2 item). $\xi$ is a Brownian motion on $[0,\infty)$, $Z(\omega)$ is the second component of the reflection pair of $\xi(\omega)$, and the convergence concerns the restriction to $[0,1]$; the statement is made for every such $(\xi,Z)$. Weak convergence in $D$ is in coupling form with Skorohod (J$_1$) convergence.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), p. 447, Theorem 1 (with the Definition of ξ and Z on the same page)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

namespace Reiman84.QueueLength

open Filter Topology MeasureTheory

/-- Theorem 1, p. 447: if (20)–(26) hold, then `Zⁿ ⇒ Z` in `D` as `n → ∞`, where
`Zⁿ(t) = n^{-1/2} Qⁿ(nt)` (`0 ≤ t ≤ 1`) and `Z = φ(ξ)` is the reflection (Lemma 1, matrix
`I − P`) of a `K`-dimensional Brownian motion `ξ` with drift `c`, covariance `𝒜` of
(27)–(28) and `ξ(0) = 0`. -/
theorem queue_length_heavy_traffic_limit {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ)
    (hQ : ∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (ξ Z : Ω' → ℝ → Fin K → ℝ)
    (hξ : IsDriftedBM c (covA lam a mu s R) P' ξ)
    (hZ : ∀ ω, ∃ y, IsReflectionPair R (ξ ω) y (Z ω)) :
    WeakConvD P (fun n ω => diffScale n (Q n ω)) P' Z := by sorry

end Reiman84.QueueLength
