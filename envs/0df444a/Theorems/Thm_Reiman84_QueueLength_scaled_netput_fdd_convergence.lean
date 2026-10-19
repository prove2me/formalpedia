-- Prove2me | Theorems.Thm_Reiman84_QueueLength_scaled_netput_fdd_convergence
-- name    : Reiman84.QueueLength.scaled_netput_fdd_convergence
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-18T12:57:44.369041+00:00
-- url     : https://prove2.me/theorems/2b0ec09f-a540-4441-b7e8-7732f30905e7
-- title:
--   Finite-dimensional convergence of the scaled netput $\zeta^n$ to the drifted Brownian motion $\zeta$
-- statement:
--   Consider a sequence of networks of §2 satisfying (20)–(26), let $\zeta^n(t)=n^{-1/2}X^n(nt)$ be the scaled netput, and let $\zeta$ be a $K$-dimensional Brownian motion with drift $c$ and covariance matrix $\mathcal A$ of (27)–(28). Then the finite-dimensional distributions of $\zeta^n$ converge to those of $\zeta$: for all $\tau_1,\dots,\tau_m\in[0,1]$ and every bounded Lipschitz $f$,
--
--   $$E_n f\big(\zeta^n(\tau_1),\dots,\zeta^n(\tau_m)\big)\longrightarrow E f\big(\zeta(\tau_1),\dots,\zeta(\tau_m)\big).$$
--
--   Role: the finite-dimensional part of the functional CLT for the netput (Proposition 3), which together with tightness yields Proposition 5.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), https://doi.org/10.1287/moor.9.3.441, Lemmas 3–5 and Proposition 3, pp. 448–449 (finite-dimensional part)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

open Filter Topology MeasureTheory

namespace Reiman84.QueueLength

theorem scaled_netput_fdd_convergence {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (ζ : Ω' → ℝ → Fin K → ℝ)
    (hζ : IsDriftedBM c (covA lam a mu s R) P' ζ)
    (m : ℕ) (τ : Fin m → ℝ) (hτ : ∀ i, τ i ∈ Set.Icc (0:ℝ) 1)
    (f : (Fin m → Fin K → ℝ) → ℝ) (hfC : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (hfL : ∃ L : NNReal, LipschitzWith L f) :
    Tendsto (fun n => ∫ ω, f (fun i => diffScale n (fun t => (net n).X t ω) (τ i)) ∂(P n))
      atTop (𝓝 (∫ ω, f (fun i => ζ ω (τ i)) ∂P')) := by sorry

end Reiman84.QueueLength
