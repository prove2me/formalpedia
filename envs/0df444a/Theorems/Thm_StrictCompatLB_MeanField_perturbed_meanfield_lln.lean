-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_perturbed_meanfield_lln
-- name    : StrictCompatLB.MeanField.perturbed_meanfield_lln
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-18T05:38:08.347909+00:00
-- url     : https://prove2.me/theorems/b9404f7f-a683-43cc-be88-609ee1466e72
-- title:
--   Perturbed mean-field LLN: an LB process whose aggregate routing stays close to $p(x)$ follows the ODE (4.2)
-- statement:
--   Let $0<\lambda<1$ and let $M_N\ge 1$ dispatchers serve $N$ servers. Let `route N w z v` be ANY routing law (for every dispatcher $w$ and state $z$ a probability vector over the servers $v$), and let $\Phi_N$ be the load-balancing process (`IsLBProcess`: uniformized chain with arrival rate $\lambda N$, unit-rate departures, an arrival at a uniform dispatcher $w$ joining server $v$ with probability `route N w z v`) started from $z_0(N)$. Let $p$ be a Lipschitz assignment function, $q_0\in\mathcal Y$ with $\|q(z_0(N))-q_0\|_1\to 0$, and let $s$ be the solution of the mean-field ODE (4.2) with $s(0)=q_0$, $s(t)\in\mathcal Y$. Write
--   $$A_N(z)_i=\frac1{M_N}\sum_{w}\sum_{v:\,z_v=i}\mathrm{route}_N(w,z,v)$$
--   for the level-aggregated arrival law (the probability that an arriving task joins a server with queue length $i$). Fix $T\ge0$ and suppose that for every $\eta>0$
--   $$\mathbb P\Big(\exists t\in[0,T]:\ \|A_N(\Phi_N(t))-p(x(\Phi_N(t)))\|_1\ge\eta\Big)\to0 .$$
--   Then for every $\varepsilon>0$
--   $$\mathbb P\Big(\sup_{t\in[0,T]}\|q(\Phi_N(t))-s(t)\|_1\ge\varepsilon\Big)\to0 .$$
--
--   Role: this is the law-of-large-numbers step of the proof of Theorem 4.3: once the dispatchers' aggregate routing is shown to be close to the mean-field assignment $p(x)$ (which Proposition 4.5 provides on proportionally sparse graphs), the occupancy process follows the fluid trajectory (4.2) uniformly on compact time intervals in probability.
--
--   **Formalization Note**: the routing law is arbitrary (only nonnegativity and unit row sums are assumed); the closeness of the aggregated arrival law to $p(x)$ is a hypothesis, stated with the $\ell_1$ distance `l1dist` of the PowerOfD fluid library, as in Theorem 4.3.
-- source:
--   D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, Section 4.1, proof of Theorem 4.3, p. 19-20 (the step 'fairly standard ([17, Ch. 8])': with the arrival law close to p(x), the occupancy process converges to the solution of (4.2)); cf. S. N. Ethier, T. G. Kurtz, Markov Processes, Ch. 11, Theorem 2.1 (Kurtz's law of large numbers for density-dependent chains)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

theorem perturbed_meanfield_lln (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (route : (N : ℕ) → Fin (M N) → (Fin N → ℕ) → Fin N → ℝ)
    (hroute : ∀ N, 1 ≤ N → (∀ w z v, 0 ≤ route N w z v) ∧ ∀ w z, ∑ v, route N w z v = 1)
    (p : (ℕ → ℝ) → ℕ → ℝ) (hp : IsAssignmentFn p) (hLip : IsLipschitzPolicy p)
    (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ) (hq₀ : InY q₀)
    (hinit : Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0))
    (s : ℝ → ℕ → ℝ) (hs : IsPiTrajectory lam p s) (hsY : ∀ t : ℝ, 0 ≤ t → InY (s t))
    (hs0 : s 0 = q₀)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ)
    (hproc : ∀ N, 1 ≤ N → IsLBProcess P lam M N (route N) (z₀ N) (Y N) (τ N))
    (T : ℝ) (hT : 0 ≤ T)
    (hlev : ∀ η : ℝ, 0 < η → Tendsto (fun N => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal η ≤ PowerOfDUniversality.Fluid.l1dist
        (fun i => (1 / (M N : ℝ)) * ∑ w : Fin (M N),
          ∑ v ∈ Finset.univ.filter (fun v => statePath (Y N) (τ N) ω t v = i),
            route N w (statePath (Y N) (τ N) ω t) v)
        (p (geqd (statePath (Y N) (τ N) ω t)))}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
        PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
      atTop (𝓝 0) := by sorry

end StrictCompatLB.MeanField
