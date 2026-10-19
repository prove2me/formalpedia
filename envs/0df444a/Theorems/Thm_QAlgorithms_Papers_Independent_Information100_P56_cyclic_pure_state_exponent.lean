-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_cyclic_pure_state_exponent
-- name    : QAlgorithms.Papers.Independent.Information100.P56.cyclic_pure_state_exponent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:23:15.042955+00:00
-- url     : https://prove2.me/theorems/305f235c-74b7-417f-8c9b-5055935d8282
-- title:
--   Section VI A, Eqs.(46)–(47): cyclic pure-state exponent
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. A code of length $N\ge1$ maps a uniform index in a set of size $K=ML$ to a word in $G^N$. A finite nonempty balanced universal$_2$ family hashes these indices onto $M$ messages, with every fiber of size $L\ge1$. Its public seed is independent and uniform. To send a uniform secret message, draw uniformly within its hash fiber and independently randomize each channel input by noise with law $P_1$. The induced Eve states are $\omega_v=\rho_E(L_vP_1)$; $\delta_N^E$ denotes full trace-norm leakage, without a factor $1/2$. Let $G=\mathbb Z_d$, $d\ge1$, with diagonal phases $U(x)|j\rangle=e^{2\pi ijx/d}|j\rangle$ and pure seed $|\psi\rangle=\sum_j\sqrt{q_j}|j\rangle$, where $q$ is a probability law. Take point-mass noise and uniform outer law. For $t>0$, the support-aware comparison trace is minimized by $P_J(j)=q_j^{(1+t)/(1+2t)}/\sum_kq_k^{(1+t)/(1+2t)}$, and its minimum is
--
--   $$\left(\sum_jq_j^{(1+t)/(1+2t)}\right)^{1+2t}.$$
--
--   For coding length $N\ge1$, leakage is bounded by the minimum over $t\in[0,1]$ of
--
--   $$2^{(1-t)/(1+t)}e^{-tN\rho_{{\rm sac},N}/(1+t)}\left(\sum_jq_j^{(1+t)/(1+2t)}\right)^{N(1+2t)/(1+t)}.$$
--
--   The endpoint value is $2$. Zero-probability indices receive zero optimizing weight, while missing positive support has infinite objective.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 13, Section VI A, Eqs.(46)–(47): cyclic pure-state exponent

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section VI A, pp.13–14, Eqs.(46)–(47): the optimizing weights and exact cyclic
trace minimum for t>0, and the complete uniform-scheme leakage bound for 0<=t<=1. -/
theorem cyclic_pure_state_exponent
    (d : ℕ) (hd : 0 < d) (q : Fin d → ℝ) (hq : IsLaw q)
    (N K M L : ℕ) (hN : 1 ≤ N) (H : BalancedHash K M L)
    (phi : Fin K → Fin N → ZMod d) :
    (∀ t : ℝ, 0 < t →
      IsLaw (cyclicOptimizer q t) ∧
      reverseSandwichedTrace (1 + t) (cyclicOutput q 0)
        (Matrix.diagonal (fun j => (cyclicOptimizer q t j : ℂ))) =
          ENNReal.ofReal (Real.rpow (∑ j, Real.rpow (q j) ((1 + t) / (1 + 2 * t))) (1 + 2 * t)) ∧
      (∀ P : Fin d → ℝ, IsLaw P →
        ENNReal.ofReal (Real.rpow (∑ j, Real.rpow (q j) ((1 + t) / (1 + 2 * t))) (1 + 2 * t)) ≤
          reverseSandwichedTrace (1 + t) (cyclicOutput q 0)
            (Matrix.diagonal (fun j => (P j : ℂ))))) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      expectedLeakage H phi (cyclicOutput q) ≤ cyclicExponent q N L t) ∧
    (∃ t ∈ Set.Icc (0 : ℝ) 1,
      expectedLeakage H phi (cyclicOutput q) ≤ cyclicExponent q N L t ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, cyclicExponent q N L t ≤ cyclicExponent q N L s) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
