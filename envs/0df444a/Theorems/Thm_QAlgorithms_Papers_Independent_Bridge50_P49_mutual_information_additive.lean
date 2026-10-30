-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P49_mutual_information_additive
-- name    : QAlgorithms.Papers.Independent.Bridge50.P49.mutual_information_additive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:26:00.522879+00:00
-- url     : https://prove2.me/theorems/33e0c79a-80c3-4eb8-9f36-ef13dc84778f
-- title:
--   Additivity of Rényi mutual information
-- statement:
--   Let $\rho_{AB}$ and $\rho'_{A'B'}$ be arbitrary density matrices on finite-dimensional bipartite spaces. For real $\alpha>1$, define $I_\alpha(A;B)=\inf_{\sigma_B}D_\alpha(\rho_{AB}\|\rho_A\otimes\sigma_B)$ over all density matrices $\sigma_B$, using natural logarithms. At $\alpha=1$, set $I_1(A;B)=S(\rho_A)+S(\rho_B)-S(\rho_{AB})$, where $S$ is von Neumann entropy in natural units. For all real $\alpha\geq1$, form the product state and regroup its factors as $AA':BB'$. Then
--
--   $$I_\alpha(AA';BB')_{\rho\otimes\rho'}=I_\alpha(A;B)_\rho+I_\alpha(A';B')_{\rho'}.$$
--
--   The composite reference optimization allows every density on $BB'$, including correlated references. The product state is constructed from the two given states.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, PDF p. 12, Theorem 11: additivity of α-Rényi mutual information

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

/-- Beigi, arXiv:1306.5920v6, Theorem 11, PDF p.12: all real a >= 1,
including ordinary quantum mutual information at one. The product is constructed. -/
theorem mutual_information_additive {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (a : ℝ) (ha : 1 ≤ a) (rho : Mat (A × B)) (eta : Mat (C × D))
    (hrho : IsDensityMatrix rho) (heta : IsDensityMatrix eta) :
    beigiRenyiMutualInformation a (groupedProduct rho eta) =
      beigiRenyiMutualInformation a rho + beigiRenyiMutualInformation a eta := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P49

end
