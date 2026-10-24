-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P20_oneShotCapacity_halfError
-- name    : QAlgorithms.Papers.Independent.Support50.P20.oneShotCapacity_halfError
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:33:58.311005+00:00
-- url     : https://prove2.me/theorems/0417f258-734c-46a6-936f-46739dd1b57a
-- title:
--   Half-error specialization of the one-shot lower bound
-- statement:
--   Let $W:x\mapsto\rho_x$ be an arbitrary classical-quantum channel on a nonempty input set, with normalized trace-class output states. Let $C_\epsilon(W)$ be the extended supremum of rates $\log_2 m$ of finite-message codes with complete decoding POVMs and average error at most $\epsilon$. For a discrete input law $P$, define the joint state $\pi_P^{AB}=\sum_xP(x)|x\rangle\langle x|\otimes\rho_x$ and its marginals $\pi_P^A,\pi_P^B$. For $0<\epsilon<1$,
--
--   $$
--   C_\epsilon(W)\ge\sup_P D_H^{\epsilon/2}(\pi_P^{AB}\|\pi_P^A\otimes\pi_P^B)-\log_2(1/\epsilon)-4.
--   $$
--
--   This is the specialization of Theorem 1 obtained by taking the auxiliary error parameter equal to half the coding error. All logarithms and rates are in bits.
-- source:
--   One-Shot Classical-Quantum Capacity and Hypothesis Testing, arXiv:1007.5456v3, PDF p. 2, Remark 1, (4): epsilon_prime=epsilon/2 one-shot lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20

noncomputable section

open Filter

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P20

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace State)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF pp.2–3, Remark 1, (4): the epsilonPrime=epsilon/2 lower bound in bits. -/
theorem oneShotCapacity_halfError {X I : Type*} [Nonempty X]
    (b : HilbertBasis I ℂ H) (W : ClassicalInputChannel X b) (epsilon : ℝ)
    (hZero : 0 < epsilon) (hOne : epsilon < 1) :
    optimizedTestingInformation b W (epsilon / 2) -
      (logTwo (1 / epsilon) : ℝ) - 4 ≤ oneUseCodeCapacity b W epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P20

end
