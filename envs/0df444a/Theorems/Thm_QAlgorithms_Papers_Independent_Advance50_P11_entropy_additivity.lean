-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P11_entropy_additivity
-- name    : QAlgorithms.Papers.Independent.Advance50.P11.entropy_additivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:26:33.093709+00:00
-- url     : https://prove2.me/theorems/8d64f331-35b0-494d-9661-43dd2420fdca
-- title:
--   Additivity of both historical fixed-reference entropies
-- statement:
--   All registers are finite dimensional and have positive dimension. Density operators are positive semidefinite with trace one, pure vectors have norm one, and logarithms are base two. Here $H_{\min}(\rho_{AB}\mid\sigma_B)$ is the fixed-reference min entropy, and $H_{\max}(\rho_{AB}\mid\sigma_B)$ is the historical support-rank max entropy, $\log_2\operatorname{tr}[(I_A\otimes\sigma_B)\Pi_{\rho_{AB}}]$, where $\Pi_\rho$ is the support projector. A conditioning register in place of a reference density means a supremum over normalized reference densities. For density operators $\rho_{AB},\rho_{A^{\prime}B^{\prime}},\sigma_B,\sigma_{B^{\prime}}$, both identities hold:
--
--   $$
--   \begin{aligned}
--   H_{\min}(\rho_{AB}\otimes\rho_{A^{\prime}B^{\prime}}\mid\sigma_B\otimes\sigma_{B^{\prime}})&=H_{\min}(\rho_{AB}\mid\sigma_B)+H_{\min}(\rho_{A^{\prime}B^{\prime}}\mid\sigma_{B^{\prime}}),\\
--   H_{\max}(\rho_{AB}\otimes\rho_{A^{\prime}B^{\prime}}\mid\sigma_B\otimes\sigma_{B^{\prime}})&=H_{\max}(\rho_{AB}\mid\sigma_B)+H_{\max}(\rho_{A^{\prime}B^{\prime}}\mid\sigma_{B^{\prime}}).
--   \end{aligned}
--   $$
--
--   The tensor product is grouped as $AA^{\prime}:BB^{\prime}$. Unsupported references and zero support overlap have entropy $-\infty$.
--
--   These are fixed-reference additivity statements, including their extended endpoints.
-- source:
--   Single-shot Quantum State Merging, arXiv:0912.4495v1, PDF p. 11, Lemma 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P11

open QAlgorithms MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Support50.P21
  (conditionalMin conditionalMax hMin hMax largestEigenvalue)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog supportRank tr)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC marginalAR)

open QAlgorithms.Papers.Independent.Information100.P22 (bell mixed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 3.7, PDF p.11, (3.9) AND (3.10): fixed-reference additivity.
Regroup AA':BB'; EReal preserves unsupported-reference minus infinity. -/
theorem entropy_additivity {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (tau : Matrix (C × D) (C × D) ℂ)
    (sigma : Matrix B B ℂ) (eta : Matrix D D ℂ)
    (hrho : IsDensityMatrix rho) (htau : IsDensityMatrix tau)
    (hsigma : IsDensityMatrix sigma) (heta : IsDensityMatrix eta) :
    conditionalMin (tensorRegroup rho tau) (Matrix.kronecker sigma eta) =
      conditionalMin rho sigma + conditionalMin tau eta ∧
    conditionalMax (tensorRegroup rho tau) (Matrix.kronecker sigma eta) =
      conditionalMax rho sigma + conditionalMax tau eta := by sorry

end QAlgorithms.Papers.Independent.Advance50.P11

end
