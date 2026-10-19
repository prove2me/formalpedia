-- Prove2me | Theorems.Thm_Reiman84_QueueLength_primitive_netput_modulus_tight
-- name    : Reiman84.QueueLength.primitive_netput_modulus_tight
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-18T12:58:15.160419+00:00
-- url     : https://prove2.me/theorems/19f1c14a-e947-4686-8d26-e297332e6023
-- title:
--   Modulus tightness of the scaled centred arrival and service-routing processes under heavy traffic
-- statement:
--   Consider a sequence of networks of §2 satisfying (20)–(26). Let $\tilde A^n$ be the centred arrival process and $\tilde S^n_k$ the centred service-routing process of station $k$ (eq. (10)). Then $n^{-1/2}\tilde A^n(n\cdot)$ and every $n^{-1/2}\tilde S^n_k(n\cdot)$ satisfy the modulus condition on $[0,1]$: for all $\varepsilon,\eta>0$ there are $\delta>0$ and $N$ such that for $n\ge N$
--
--   $$P_n\Big\{\sup_{u,t\in[0,1],\,|u-t|\le\delta}\big\|n^{-1/2}\tilde A^n(nu)-n^{-1/2}\tilde A^n(nt)\big\|\ge\varepsilon\Big\}\le\eta,$$
--
--   and likewise for each $\tilde S^n_k$.
--
--   Role: tightness of the primitive processes; it gives the tightness of the netput $\zeta^n$ and, with Proposition 4, the uniform closeness of $\tilde\zeta^n$ and $\zeta^n$.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), https://doi.org/10.1287/moor.9.3.441, Lemmas 3–5 and Proposition 3, pp. 448–449 (tightness part of the functional CLT for the primitive processes); criterion: Billingsley, Convergence of Probability Measures, 2nd ed., Wiley 1999, Theorem 7.3

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

open MeasureTheory

namespace Reiman84.QueueLength

theorem primitive_netput_modulus_tight {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c) :
    (∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ u ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |u - t| ≤ δ ∧
        ε ≤ ‖diffScale n (fun r => (net n).Atilde r ω) u -
          diffScale n (fun r => (net n).Atilde r ω) t‖} ≤ ENNReal.ofReal η) ∧
    ∀ k : Fin K, ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ u ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |u - t| ≤ δ ∧
        ε ≤ ‖diffScale n (fun r => (net n).Stilde k r ω) u -
          diffScale n (fun r => (net n).Stilde k r ω) t‖} ≤ ENNReal.ofReal η := by sorry

end Reiman84.QueueLength
