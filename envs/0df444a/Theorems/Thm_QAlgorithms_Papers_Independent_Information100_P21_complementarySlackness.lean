-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_complementarySlackness
-- name    : QAlgorithms.Papers.Independent.Information100.P21.complementarySlackness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:52:58.222792+00:00
-- url     : https://prove2.me/theorems/05ccf2c5-3c03-48e2-a10a-6cc477c8c7c8
-- title:
--   III.11 — Lemma III.11 (Complementary slackness). If Y is any generalized-primal optimum and W∗ any generalized-dual
-- statement:
--   Let $\rho$ be a two-qubit state, $Y$ any generalized-primal optimum, and $W$ any generalized-dual optimum. For $H=I-W^\Gamma$ and $S=\rho^\Gamma+Y^\Gamma$,
--   $$HY=0,\qquad WS=0.$$
--   The conclusions hold for every pair of optima, without selecting a matching pair.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 10, III.11 — Lemma III.11 (Complementary slackness). If Y is any generalized-primal optimum and W∗ any generalized-dual

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 10, Lemma III.11 (Complementary slackness). If Y is any generalized-primal optimum and W∗ any generalized-dual. -/
theorem complementarySlackness (rho Y W : Op QQ) (h : QAlgorithms.IsDensityMatrix rho)
  (hY : optG rho Y) (hW : optDG rho W) :
  (1-pt W)*Y=0 ∧ W*(pt rho+pt Y)=0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
