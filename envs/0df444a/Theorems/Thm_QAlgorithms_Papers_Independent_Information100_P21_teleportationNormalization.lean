-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_teleportationNormalization
-- name    : QAlgorithms.Papers.Independent.Information100.P21.teleportationNormalization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:09:55.983484+00:00
-- url     : https://prove2.me/theorems/c20aefda-524e-4c1f-88f1-ff5a7277dbe0
-- title:
--   VIII — standard-robustness teleportation normalization
-- statement:
--   Let $\rho$ be a two-qubit state. Let $F^*_{\rm TP-LOCC}$ be its optimized deterministic LOCC singlet fraction and let $f^*_{\rm tel}$ be its optimal Haar-mean qubit teleportation fidelity. Then
--   $$R_s(\rho)=R_g(\rho)=2F^*_{\rm TP-LOCC}(\rho)-1=3f^*_{\rm tel}(\rho)-2.$$
--   Both quantities optimize actual adaptive local Kraus protocols, using supremal finite-round values to allow protocol limits. The new identification is with the standard separable-noise cost; the generalized and fidelity relations are credited to Refs. [15,24].
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 17, VIII — standard-robustness teleportation normalization

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 17, standard-robustness teleportation normalization. -/
theorem teleportationNormalization (rho : Op QQ) (h : QAlgorithms.IsDensityMatrix rho) :
  rs rho=rg rho ∧ rs rho=2*singletFraction rho-1 ∧
  rs rho=3*teleportFidelity rho-2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
