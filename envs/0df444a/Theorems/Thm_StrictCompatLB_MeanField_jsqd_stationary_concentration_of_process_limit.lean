-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_jsqd_stationary_concentration_of_process_limit
-- name    : StrictCompatLB.MeanField.jsqd_stationary_concentration_of_process_limit
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:02:43.519597+00:00
-- url     : https://prove2.me/theorems/88950598-e5fb-438f-ba43-786cdacbaa07
-- title:
--   Process-level limit plus tightness gives concentration of the JSQ(d) stationary laws
-- statement:
--   Interchange of limits for JSQ(d) under compatibility constraints. Let $0<\lambda<1$, $d\ge2$, server pools $M$ and compatibility graphs $G$ with stochastic JSQ(d) kernels. Assume (i) the load-balancing process exists from every initial state; (ii) the process-level mean-field limit holds: whenever the initial occupancies converge in $\ell_1$ to $q_0\in Y$ and $s$ is the ODE trajectory from $q_0$, then for every realisation of the processes on a common probability space, $P(\sup_{t\le T}\|q^N(t)-s(t)\|_1\ge\varepsilon)\to0$; (iii) every $q_0\in Y$ starts a $Y$-valued trajectory; (iv) weights $\omega_i>0$ that are geometric with ratio $r\in(1,2/(1+\lambda))$ beyond some index $i_0$, for which the weighted potential decays exponentially along every $Y$-valued trajectory. Then for stationary laws $\pi_N$ ($N\ge N_0$) that are tight for the weights $\omega$, $\pi_N(\|q^N-q^*\|_1\ge\varepsilon)\to0$ for every $\varepsilon>0$, where $q^*$ is the fixed point.
--
--   Role: the interchange-of-limits step proving the steady-state part (conjecture 2) of the parent from conjecture 1, tightness and the potential decay.
-- source:
--   D. Rutten, D. Mukherjee, Load Balancing Under Strict Compatibility Constraints, https://arxiv.org/abs/2008.07562, Section 4.4 (proof of Theorem 3.4, interchange of limits), p. 23, using the potential decay of Theorem 4.11 and tightness (4.27)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StrictCompatLB.MeanField

theorem jsqd_stationary_concentration_of_process_limit : ∀ (lam : ℝ), 0 < lam → lam < 1 → ∀ (d : ℕ), 2 ≤ d →
  ∀ (M : ℕ → ℕ), (∀ N, 0 < M N) → ∀ (G : (N : ℕ) → Finset (Fin N × Fin (M N))),
  (∀ N, 1 ≤ N → IsStochasticKernel (jsqdKernel lam d M G N)) →
  (∀ (lam' : ℝ), 0 < lam' → ∀ (M' : ℕ → ℕ) (N : ℕ), 1 ≤ N →
    ∀ (route : Fin (M' N) → (Fin N → ℕ) → Fin N → ℝ),
      (∀ z, HasSum (lbKernel lam' M' N route z) 1) → (∀ z z', 0 ≤ lbKernel lam' M' N route z z') →
      ∀ z₀ : Fin N → ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (Y : ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → Ω → ℝ),
        IsLBProcess P lam' M' N route z₀ Y τ) →
  (∀ (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ), InY q₀ →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
        (∀ t : ℝ, 0 ≤ t → InY (s t)) → s 0 = q₀ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
          (∀ N, 1 ≤ N → IsLBProcess P lam M N (jsqdRoute M G N d) (z₀ N) (Y N) (τ N)) →
          ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
              atTop (𝓝 0)) →
  (∀ q₀ : ℕ → ℝ, InY q₀ → ∃ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s ∧
      (∀ t : ℝ, 0 ≤ t → InY (s t)) ∧ s 0 = q₀) →
  ∀ (ω : ℕ → ℝ), (∀ i, 1 ≤ i → 0 < ω i) → ∀ (r : ℝ), 1 < r → r < 2 / (1 + lam) →
  ∀ (i₀ : ℕ), (∀ i : ℕ, 1 ≤ i → ω (i₀ + i) = ω i₀ * r ^ i) →
  ∀ (δ : ℝ), 0 < δ → (∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
      (∀ t : ℝ, 0 ≤ t → InY (s t)) → ∀ t : ℝ, 0 ≤ t →
        PowerTwoChoices.Limit.potential lam d ω (s t) ≤
          ENNReal.ofReal (Real.exp (-δ * t)) * PowerTwoChoices.Limit.potential lam d ω (s 0)) →
  ∀ (N₀ : ℕ), 1 ≤ N₀ → ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
    (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) → IsTightWeighted ω N₀ π →
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => probOf (π N) {z | ENNReal.ofReal ε ≤
          PowerOfDUniversality.Fluid.l1dist (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)})
        atTop (𝓝 0) := by sorry

end StrictCompatLB.MeanField
