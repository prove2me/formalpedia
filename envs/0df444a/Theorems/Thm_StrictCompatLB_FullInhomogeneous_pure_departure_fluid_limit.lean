-- Prove2me | Theorems.Thm_StrictCompatLB_FullInhomogeneous_pure_departure_fluid_limit
-- name    : StrictCompatLB.FullInhomogeneous.pure_departure_fluid_limit
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T21:16:11.492797+00:00
-- url     : https://prove2.me/theorems/8e1721c5-a307-49b2-b606-7991dede45f2
-- title:
--   Fluid limit of the load-balancing chain with no arrivals ($\lambda = 0$)
-- statement:
--   Let $\lambda = 0$ (no arrivals). For any dispatcher counts $M_N>0$, any routing rule, deterministic initial states $z_N$ with $\|\mathrm{occ}(z_N)-q_0\|_1\to 0$, $q_0\in\mathcal Y$, and any trajectory $s$ of the supermarket ODE at $\lambda=0$ (i.e. $\dot s_i = -(s_i - s_{i+1})$, $i\ge1$) with $s(t)\in\mathcal Y$ and $s(0)=q_0$: if $(Y_N,\tau_N)$ realizes the uniformized load-balancing chain of rate $N$ started at $z_N$, then for every $T\ge0$, $\varepsilon>0$, $P(\sup_{t\le T}\|\mathrm{occ}(X_N(t))-s(t)\|_1\ge\varepsilon)\to0$.
--
--   Proof idea: at $\lambda=0$ the jump kernel does not depend on the routing rule, so the chain equals the one with uniform routing, whose routed level distribution is exactly the global empirical distribution; the perturbed mean-field law of large numbers (Azuma bounds on the occupancy martingales, Gronwall on the $\ell_1$-Lipschitz drift, exponential-clock concentration) with the identity assignment function then gives the limit.
-- source:
--   D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, Theorem 3.4 p. 12 (case lambda = 0) and the proof of Theorem 4.3 (Section 5); S. N. Ethier, T. G. Kurtz, Markov Processes (Wiley 1986), Chapter 11, Theorem 2.1

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_CountableChain
import Definitions.Def_StrictCompatLB_MeanField_Model
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

open MeasureTheory Filter Topology
open StrictCompatLB.MeanField
open scoped ENNReal

namespace StrictCompatLB.FullInhomogeneous

theorem pure_departure_fluid_limit (d : ℕ) (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (s : ℝ → ℕ → ℝ) (hs : PowerTwoChoices.Limit.IsTrajectory 0 d s)
    (hsY : ∀ t : ℝ, 0 ≤ t → InY (s t)) (hs0 : s 0 = q₀)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P 0 M N (route N) (z₀ N) (Y N) (τ N))
    (T : ℝ) (hT : 0 ≤ T) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
      atTop (𝓝 0) := by sorry

end StrictCompatLB.FullInhomogeneous
