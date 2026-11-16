-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_lemma_B_5
-- name    : TransparencyTeamContracts.Submodular.Supplement.lemma_B_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:21:30.950897+00:00
-- url     : https://prove2.me/theorems/f51728e7-5648-402e-868a-6004127b5df8
-- title:
--   Lemma B.5 (used in the proof of Theorem B.1) — Cost monotonicity of the exact ratio
-- statement:
--   For every $k\ge0$ and $X\ge1$, define $m_0,m_1$ and the full-disclosure denominator $D_F$ as in equation (21), and let
--   $$R(c;k,X)=\frac{m_1(1-c/(m_1-m_0))}{D_F}.$$
--   Then $R$ is non-increasing in $c$ throughout the entire feasible positive-denominator domain:
--   $$0<c,\qquad kc\le1,\qquad cX^2\le1,\qquad D_F>0.$$
--   The definition is exactly the printed effort branch, without adding a maximum with the no-effort branch. The domain includes $k=0$ and $X=1$ when their payoff denominator is positive.
--
--   Differences from the source:
--   - encoding: 0<c<=min{1/k,1/X^2}, taking 1/k=+infinity at k=0, wherever the denominator is positive → 0<c, k*c<=1, c*X^2<=1 and positive fullDenominator; reason: for k>=0 and X>=1 these are equivalent constraints and preserve the k=0 endpoint without Lean real division by zero
--   - encoding: R is non-increasing in c → AntitoneOn on the feasible set; reason: this compares every ordered pair of feasible positive-denominator costs, including the boundary costs
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Lemma B.5, printed p. 29 (PDF p. 31)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_SingleAgent

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Lemma B.5, printed 29 / PDF 31. The k=0 endpoint has no artificial 1/0 bound. -/
theorem lemma_B_5 (k X : ℝ) (hk : 0 ≤ k) (hX : 1 ≤ X) :
    AntitoneOn (fun c => R c k X) {c | RatioDomain k X c} := by sorry

end TransparencyTeamContracts.Submodular.Supplement
