-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P20_oneShotCapacity_bounds
-- name    : QAlgorithms.Papers.Independent.Support50.P20.oneShotCapacity_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:30:19.329022+00:00
-- url     : https://prove2.me/theorems/737cd40e-0812-47cd-8e16-1f88ebdb84e9
-- title:
--   Two-sided one-shot classical-quantum capacity bounds
-- statement:
--   Let $W:x\mapsto\rho_x$ be any channel from a nonempty classical set $X$ to normalized positive trace-class operators on a complex Hilbert space $B$. A code has an integer number $m\ge1$ of equiprobable messages, an arbitrary encoder, and a complete $m$-outcome POVM; its rate is $\log_2m$ and its error is average decoding error. Let $C_\epsilon(W)$ be the extended supremum of rates of codes with error at most $\epsilon$. For a discrete input law $P$, set $\pi_P^{AB}=\sum_xP(x)|x\rangle\langle x|\otimes\rho_x$, with marginals $\pi_P^A,\pi_P^B$, and write $I_H^\delta(P,W)=D_H^\delta(\pi_P^{AB}\|\pi_P^A\otimes\pi_P^B)$. Here $D_H^\delta(\rho\|\sigma)=-\log_2\inf_{0\le Q\le I,\,\operatorname{Tr}(Q\rho)\ge1-\delta}\operatorname{Tr}(Q\sigma)$, with $-\log_2 0=+\infty$. If $0<\epsilon'<\epsilon<1$, then
--
--   $$
--   \sup_P I_H^\epsilon(P,W)\ \ge\ C_\epsilon(W)\ \ge\ \sup_P I_H^{\epsilon'}(P,W)-\log_2\frac{4\epsilon}{(\epsilon-\epsilon')^2}.
--   $$
--
--   These bounds compare the operational capacity with optimized hypothesis-testing information without a dimension, alphabet-size, or memory assumption.
--
--   **Formalization Note** The cq testing optimization uses the diagonal classical blocks of an arbitrary effect. This preserves both trace probabilities and the whole testing optimization. Capacity is defined from codes independently of the information quantity.
-- source:
--   One-Shot Classical-Quantum Capacity and Hypothesis Testing, arXiv:1007.5456v3, PDF p. 2, Theorem 1, (3): two-sided epsilon-one-shot classical-quantum capacity bounds

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

/-- PDF p.2, Theorem 1, (3): BOTH one-shot bounds, with distinct error parameters.
Capacity is an extended supremum of rates of actual finite-message codes. -/
theorem oneShotCapacity_bounds {X I : Type*} [Nonempty X]
    (b : HilbertBasis I ℂ H) (W : ClassicalInputChannel X b)
    (epsilon epsilonPrime : ℝ) (hPrime : 0 < epsilonPrime)
    (hOrder : epsilonPrime < epsilon) (hOne : epsilon < 1) :
    oneUseCodeCapacity b W epsilon ≤ optimizedTestingInformation b W epsilon ∧
    optimizedTestingInformation b W epsilonPrime -
      (logTwo (4 * epsilon / (epsilon - epsilonPrime)^2) : ℝ) ≤
        oneUseCodeCapacity b W epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P20

end
