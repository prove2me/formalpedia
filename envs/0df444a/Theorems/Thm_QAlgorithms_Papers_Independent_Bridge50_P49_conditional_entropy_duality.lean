-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P49_conditional_entropy_duality
-- name    : QAlgorithms.Papers.Independent.Bridge50.P49.conditional_entropy_duality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:24:29.546235+00:00
-- url     : https://prove2.me/theorems/f39071a5-f166-4dc4-ac26-a03a74130b37
-- title:
--   Duality of conditional Rényi entropies, including infinite orders
-- statement:
--   Let $\rho_{ABC}=|\psi\rangle\langle\psi|$ be a normalized pure state on finite-dimensional registers $A,B,C$. For orders $1/2\leq\alpha,\beta\leq\infty$ different from one, assume $1/\alpha+1/\beta=2$, with $1/\infty=0$. For a bipartite density $\omega_{AB}$, define $H_p(A|B)_\omega=-\inf_{\sigma_B}D_p(\omega_{AB}\|I_A\otimes\sigma_B)$ over all normalized density matrices $\sigma_B$. Finite-order divergence uses natural logarithms, support inverses, and $+\infty$ on support failure even below one; $D_\infty(\omega\|\eta)=\inf\{t\in\mathbb R:\omega\leq e^t\eta\}$ is max-relative entropy. For the actual marginals of $\rho_{ABC}$,
--
--   $$H_\alpha(A|B)_\rho=-H_\beta(A|C)_\rho.$$
--
--   This includes the endpoint pairs $(1/2,\infty)$ and $(\infty,1/2)$ and requires no full-rank assumption on the physical state or its marginals.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, PDF p. 10, Theorem 9 (Duality)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P49

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P49

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower Dominates rawTrace leftMarginal rightMarginal marginalAB marginalAC)

/-- Beigi, arXiv:1306.5920v6, Theorem 9, PDF pp.10--11 (stated already pp.2--3).
Includes (1/2,infinity) and its reverse; a normalized vector constructs the pure state. -/
theorem conditional_entropy_duality {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (p q : ℝ≥0∞) (hp : (1 / 2 : ℝ≥0∞) ≤ p) (hq : (1 / 2 : ℝ≥0∞) ≤ q)
    (hpone : p ≠ 1) (hqone : q ≠ 1)
    (hpq : reciprocalOrder p + reciprocalOrder q = 2)
    (psi : EuclideanSpace ℂ (A × (B × C))) (hpsi : ‖psi‖ = 1) :
    beigiConditionalRenyiEntropy p (marginalAB (pureDensity psi)) =
      -beigiConditionalRenyiEntropy q (marginalAC (pureDensity psi)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P49

end
