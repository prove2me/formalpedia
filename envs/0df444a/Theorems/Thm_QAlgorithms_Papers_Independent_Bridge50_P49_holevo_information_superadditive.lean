-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P49_holevo_information_superadditive
-- name    : QAlgorithms.Papers.Independent.Bridge50.P49.holevo_information_superadditive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:26:36.505705+00:00
-- url     : https://prove2.me/theorems/2f500d5d-4f44-4b73-96b1-631f65f107fc
-- title:
--   Superadditivity of Rényi Holevo information
-- statement:
--   Let $\Phi_{A\to B}$ and $\Phi'_{A'\to B'}$ be quantum channels between finite-dimensional, nonzero Hilbert spaces. For each real $\alpha\geq1$, define $\chi_\alpha(\Phi)=\sup I_\alpha(X;B)$ over every finite ensemble of mixed input densities $\{p_x,\rho_x\}$, where $p_x\geq0$, $\sum_xp_x=1$, and the output state is $\sum_xp_x|x\rangle\langle x|\otimes\Phi(\rho_x)$. Here $I_\alpha$ is the natural-log sandwiched Rényi mutual information and $I_1$ is ordinary quantum mutual information. The supremum is taken in the extended reals. Then
--
--   $$\chi_\alpha(\Phi\otimes\Phi')\geq\chi_\alpha(\Phi)+\chi_\alpha(\Phi').$$
--
--   This retains arbitrary finite alphabet sizes and nonuniform weights; it asserts superadditivity rather than equality.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, PDF p. 12, Theorem 12: super-additivity of α-Holevo information

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

/-- Beigi, arXiv:1306.5920v6, Theorem 12, PDF p.12 (abstract p.1).
The extended supremum includes all finite nonuniform ensembles of mixed inputs. -/
theorem holevo_information_superadditive {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (a : ℝ) (ha : 1 ≤ a) (Phi : Superop A B) (Psi : Superop C D)
    (hPhi : IsChannel Phi) (hPsi : IsChannel Psi) :
    beigiRenyiHolevoInformation a Phi + beigiRenyiHolevoInformation a Psi ≤
      beigiRenyiHolevoInformation a (tensorChannel Phi Psi) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P49

end
