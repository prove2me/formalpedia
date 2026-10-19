-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_supplementalEquality
-- name    : QAlgorithms.Papers.Independent.Information100.P21.supplementalEquality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:50:44.742066+00:00
-- url     : https://prove2.me/theorems/3db4b17e-fec4-454b-81b9-0d6829dde0a3
-- title:
--   II.7 — Theorem II.7. For every two-qubit density operator ρ,
-- statement:
--   For every two-qubit density operator $\rho$,
--   $$R_s(\rho)=R_g(\rho).$$
--   This is the numbered supplemental restatement of the value identity in main-text Theorem 1; its separate node is retained explicitly.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 8, II.7 — Theorem II.7. For every two-qubit density operator ρ,

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 8, Theorem II.7. For every two-qubit density operator ρ,. -/
theorem supplementalEquality (rho : Op QQ) (h : QAlgorithms.IsDensityMatrix rho) : rs rho=rg rho := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
