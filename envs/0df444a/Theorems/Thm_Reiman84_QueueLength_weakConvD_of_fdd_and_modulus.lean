-- Prove2me | Theorems.Thm_Reiman84_QueueLength_weakConvD_of_fdd_and_modulus
-- name    : Reiman84.QueueLength.weakConvD_of_fdd_and_modulus
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-18T12:57:07.708996+00:00
-- url     : https://prove2.me/theorems/e66265b6-f77c-4008-8214-485eee7af47f
-- title:
--   Finite-dimensional convergence plus modulus tightness with a continuous limit gives weak convergence in $D[0,1]$ (coupling form)
-- statement:
--   Let $X^n$ be random paths on probability spaces $(\Omega_n,P_n)$ that are almost surely cadlag on $[0,1]$ and measurable as random elements of the path space, and let $X'$ be a measurable process on $(\Omega',P')$ with continuous paths on $[0,1]$. Suppose the finite-dimensional distributions converge, in the sense that for all times $\tau_1,\dots,\tau_m\in[0,1]$ and every bounded Lipschitz $f$,
--
--   $$E_n f\big(X^n(\tau_1),\dots,X^n(\tau_m)\big)\to E' f\big(X'(\tau_1),\dots,X'(\tau_m)\big),$$
--
--   and that the modulus condition holds: for all $\varepsilon,\eta>0$ there are $\delta>0$ and $N$ with
--
--   $$P_n\Big\{\sup_{s,t\in[0,1],\,|s-t|\le\delta}\|X^n(s)-X^n(t)\|\ge\varepsilon\Big\}\le\eta\qquad(n\ge N).$$
--
--   Then $X^n\Rightarrow X'$ in $D[0,1]$, in the coupling form `WeakConvD`: there are versions on one probability space converging almost surely in the Skorohod topology.
--
--   Role: this is the general weak-convergence criterion that turns the finite-dimensional convergence and tightness of the scaled netput into the weak convergence asserted in Proposition 5.
-- source:
--   Billingsley, Convergence of Probability Measures, 2nd ed., Wiley 1999, https://doi.org/10.1002/9780470316962, Theorem 7.5 (fdd convergence + modulus condition) together with the Skorohod representation, Theorem 6.7; used in Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), https://doi.org/10.1287/moor.9.3.441, proof of Proposition 5, p. 451

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths

open Filter Topology MeasureTheory

namespace Reiman84.QueueLength

theorem weakConvD_of_fdd_and_modulus {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ → Fin K → ℝ) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') (X' : Ω' → ℝ → Fin K → ℝ)
    (hP : ∀ n, IsProbabilityMeasure (P n)) (hP' : IsProbabilityMeasure P')
    (hXa : ∀ n, AEMeasurable (fun ω => onUnit (X n ω)) (P n) ∧
      ∀ᵐ ω ∂(P n), IsCadlag01 (X n ω))
    (hX'm : ∀ t, Measurable fun ω => X' ω t) (hc : ∀ ω, ContinuousOn (X' ω) (Set.Icc 0 1))
    (hF : ∀ (m : ℕ) (τ : Fin m → ℝ), (∀ i, τ i ∈ Set.Icc (0:ℝ) 1) →
      ∀ (f : (Fin m → Fin K → ℝ) → ℝ), (∃ C : ℝ, ∀ x, |f x| ≤ C) →
        (∃ L : NNReal, LipschitzWith L f) →
        Tendsto (fun n => ∫ ω, f (fun i => X n ω (τ i)) ∂(P n)) atTop
          (𝓝 (∫ ω, f (fun i => X' ω (τ i)) ∂P')))
    (hT : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε ≤ ‖X n ω s - X n ω t‖} ≤ ENNReal.ofReal η) :
    WeakConvD P X P' X' := by sorry

end Reiman84.QueueLength
