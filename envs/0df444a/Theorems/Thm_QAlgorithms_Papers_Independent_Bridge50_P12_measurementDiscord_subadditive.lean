-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P12_measurementDiscord_subadditive
-- name    : QAlgorithms.Papers.Independent.Bridge50.P12.measurementDiscord_subadditive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:30:33.892377+00:00
-- url     : https://prove2.me/theorems/33178fd3-6d63-4afc-8337-a7b9e4e1b357
-- title:
--   Subadditivity of measurement-based quantum discord
-- statement:
--   Let $\rho^{AB}$ and $\sigma^{A'B'}$ be density operators on arbitrary nonzero finite-dimensional bipartite systems. Let $D^{\leftarrow}$ be measurement-based discord with measurements on the second party. It equals $H(B)-H(AB)$ plus the infimum of the probability-weighted conditional entropy of $A$ over all local measurement operators $\{M_k\}$ satisfying $\sum_kM_k^\dagger M_k=I_B$. Zero-probability outcomes contribute zero, and no projectivity or outcome-count bound is imposed. Then
--
--   $$D^{\leftarrow}(\rho^{AB}\otimes\sigma^{A'B'})\le D^{\leftarrow}(\rho^{AB})+D^{\leftarrow}(\sigma^{A'B'}).$$
--
--   The tensor product is grouped as $AA':BB'$. This establishes subadditivity and does not assert resource monotonicity.
-- source:
--   Asymptotically Consistent Measures of General Quantum Resources: Discord, Non-Markovianity, and Non-Gaussianity, arXiv:2103.05665v4, PDF p. 17, Proposition S16

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Bridge50.P12

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

/-- PDF p.17, Proposition S16, S64: AA':BB' subadditivity. No monotonicity
assertion is part of this statement. -/
theorem measurementDiscord_subadditive {A B A2 B2 : Type}
    [Fintype A] [Fintype B] [Fintype A2] [Fintype B2]
    [DecidableEq A] [DecidableEq B] [DecidableEq A2] [DecidableEq B2]
    [Nonempty A] [Nonempty B] [Nonempty A2] [Nonempty B2]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (A2 × B2) (A2 × B2) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    measurementDiscord (groupedBipartiteProduct rho sigma) ≤
      measurementDiscord rho + measurementDiscord sigma := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P12

end
