-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_genericPriorCounterexample
-- name    : QAlgorithms.Papers.Independent.Information100.P21.genericPriorCounterexample
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:06:06.572438+00:00
-- url     : https://prove2.me/theorems/76956f0d-9f9c-4dd0-bba1-9662e54f50b2
-- title:
--   V.A — full-rank counterexample to the generic prior formula
-- statement:
--   Let $\rho_{\rm ex}$ be the literal X state with $(a,b,c,d,w,z)=(3/8,1/5,1/20,3/8,1/4,1/100)$. It is full rank. Its sorted positive distinct Wootters numbers are $(5/8,1/8,11/100,9/100)$ and associated norms $(1,1,5/4,5/4)$; its concurrence is $3/10$. The earlier candidate is $27/80$, whereas
--   $$R_s(\rho_{\rm ex})=R_g(\rho_{\rm ex})=1/4<27/80.$$
--   The separable noise $Y_{\rm ex}=|01\rangle\langle01|/20+|10\rangle\langle10|/5$ is optimal in both problems. The feasible generalized witness $2|\beta\rangle\langle\beta|$, $\beta=(|01\rangle-|10\rangle)/\sqrt2$, has objective $1/4$. This refutes the candidate on its generic domain.
--
--   PDF p.16, S84: retain the four input eigenvalues with multiplicity via the characteristic polynomial.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 16, V.A — full-rank counterexample to the generic prior formula

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 16, full-rank counterexample to the generic prior formula.
Round-one coverage restoration: PDF p.16, S84: retain the four input eigenvalues with multiplicity via the characteristic polynomial. -/
theorem genericPriorCounterexample  :
  let lam : Fin 4 → ℝ := ![5/8,1/8,11/100,9/100]
  let K : Fin 4 → ℝ := ![1,1,5/4,5/4]
  let beta : Vec QQ := ((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket (0,1)-QAlgorithms.ket (1,0))
  QAlgorithms.IsDensityMatrix rhoEx ∧ rhoEx.PosDef ∧
  rhoEx.charpoly =
    (Polynomial.X - Polynomial.C (5/8 : ℂ)) *
    (Polynomial.X - Polynomial.C (1/8 : ℂ)) *
    (Polynomial.X - Polynomial.C ((1/8 + Real.sqrt 229/200 : ℝ) : ℂ)) *
    (Polynomial.X - Polynomial.C ((1/8 - Real.sqrt 229/200 : ℝ) : ℂ)) ∧
  (∀ i,0<lam i) ∧ Function.Injective lam ∧ Antitone lam ∧
  (∃ v : Fin 4 → Vec QQ, woottersFrame rhoEx lam v ∧ ∀ i,frameNorm lam v i=K i) ∧
  concurrence rhoEx=3/10 ∧ oldCandidate lam K=27/80 ∧
  optS rhoEx noiseEx ∧ optG rhoEx noiseEx ∧
  dualG (2 • proj beta) ∧ (-((2 • proj beta) * pt rhoEx).trace.re)=1/4 ∧
  noiseEx.trace.re=1/4 ∧ rs rhoEx=1/4 ∧ rg rhoEx=1/4 ∧ 1/4<(27/80:ℝ) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
