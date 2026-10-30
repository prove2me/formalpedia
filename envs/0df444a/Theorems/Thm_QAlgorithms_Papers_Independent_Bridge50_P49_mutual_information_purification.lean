-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P49_mutual_information_purification
-- name    : QAlgorithms.Papers.Independent.Bridge50.P49.mutual_information_purification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:25:19.030117+00:00
-- url     : https://prove2.me/theorems/e7ce824b-6cd3-4af4-bb19-86ef1e47cf07
-- title:
--   Purification variational formula for Rényi mutual information
-- statement:
--   Let $\rho_{AB}$ be a finite-dimensional density matrix with normalized purification $|\psi\rangle_{ABC}$, and put $\rho_A=\operatorname{Tr}_B\rho_{AB}$. Let real $\alpha>1$ and $1/2\leq\beta<1$ satisfy $1/\alpha+1/\beta=2$, and write $\alpha'=\alpha/(\alpha-1)$. Define $\Gamma_X^s(Y)=X^{s/2}YX^{s/2}$ with spectral support inverses. The Rényi mutual information is $I_\alpha(A;B)=\inf_{\sigma_B}D_\alpha(\rho_{AB}\|\rho_A\otimes\sigma_B)$ over density matrices $\sigma_B$, with natural logarithms. Set
--
--   $$T_B(\tau_C)=\big[(\operatorname{Tr}_A\circ\Gamma_{\rho_A}^{-1/\alpha'})\otimes\mathcal I_B\otimes(\operatorname{Tr}_C\circ\Gamma_{\tau_C}^{1/\alpha'})\big](|\psi\rangle\langle\psi|).$$
--
--   The maximum below is attained by a density matrix $\tau_C$, and
--
--   $$I_\alpha(A;B)=\alpha'\log\left(\max_{\tau_C}\|T_B(\tau_C)\|_\beta\right).$$
--
--   Both $A$ and $C$ are traced out, leaving an operator on $B$, and $\|\cdot\|_\beta$ is the Schatten norm expression, not a scalar power applied to a matrix.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, PDF p. 12, Theorem 10: purification variational formula for I_α

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

/-- Beigi, arXiv:1306.5920v6, Theorem 10, PDF pp.11--12, (24).
The maximum is a conclusion (a maximizing density and domination of every competitor).
The output of the double partial trace is on B, and the outer operation is a beta norm. -/
theorem mutual_information_purification {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (a b : ℝ) (ha : 1 < a) (hb : (1 / 2 : ℝ) ≤ b) (hbone : b < 1)
    (hab : 1 / a + 1 / b = 2) (rho : Mat (A × B)) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (A × (B × C))) (hpsi : ‖psi‖ = 1)
    (hpurification : marginalAB (pureDensity psi) = rho) :
    ∃ tau : Mat C, IsDensityMatrix tau ∧
      (∀ upsilon : Mat C, IsDensityMatrix upsilon →
        purificationObjective a b (leftMarginal rho) (pureDensity psi) upsilon ≤
          purificationObjective a b (leftMarginal rho) (pureDensity psi) tau) ∧
      beigiRenyiMutualInformation a rho =
        ((a / (a - 1) * Real.log
          (purificationObjective a b (leftMarginal rho) (pureDensity psi) tau) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P49

end
