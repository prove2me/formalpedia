-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_binary_qutrit_passive_energy_formula
-- name    : QAlgorithms.Papers.Independent.Information100.P38.binary_qutrit_passive_energy_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:12:02.110029+00:00
-- url     : https://prove2.me/theorems/3029d7d4-885b-4ec3-966f-5a28931b780c
-- title:
--   Appendix C, Eqs.(C18)–(C30)
-- statement:
--   Take $H=\operatorname{diag}(0,1,2)$, an effect $A$ with $0<V:=\operatorname{Tr}A<3$, and a density matrix $\rho$. For the binary measurement $N=\{A,I-A\}$, put $t=\operatorname{Tr}(A\rho)$, $D=\lambda_{\max}(A)-\lambda_{\min}(A)$, and $p_i=\rho_{ii}$. Its coarse-grained state is $Y=\frac{1-t}{3-V}I+(\frac tV-\frac{1-t}{3-V})A$, and
--
--   $$\begin{aligned}\lambda_{\max}(Y)-\lambda_{\min}(Y)&=D\frac{|3t-V|}{V(3-V)},\\P_H(Y)&=1-D\frac{|3t-V|}{V(3-V)},\\P_H(\Delta\rho)&=1-(p_{\max}-p_{\min}),\\P_H(\Delta\rho)-P_H(Y)&=D\frac{|3t-V|}{V(3-V)}-(p_{\max}-p_{\min}).\end{aligned}$$
--
--   More generally every qutrit density matrix $\omega$ satisfies $P_H(\omega)=1-[\lambda_{\max}(\omega)-\lambda_{\min}(\omega)]$. Here $p_{\max}$ and $p_{\min}$ are the largest and smallest diagonal populations. These formulas reduce the Appendix C optimization to populations and one outcome probability.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 14, Appendix C, Eqs.(C18)–(C30)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.14, Appendix C, Eqs.(C18)–(C30): binary qutrit coarse-grained state,
spectral width and passive energy; 0<Tr(A)<3 is the rational expression's domain. -/
theorem binary_qutrit_passive_energy_formula (A X : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : IsEffect A) (hX : IsDensityMatrix X) (hV0 : 0 < A.trace.re) (hV3 : A.trace.re < 3) :
    let V := A.trace.re
    let t := effectProb A X
    let D := ergotropicSpectralWidth A
    let Y := ergotropicCoarseGraining (ergotropicBinary A) X
    (∀ W : Matrix (Fin 3) (Fin 3) ℂ, IsDensityMatrix W →
      passiveEnergy ![0, 1, 2] W = 1 - ergotropicSpectralWidth W) ∧
    Y = (((1 - t) / (3 - V) : ℝ) : ℂ) • 1 +
      (((t / V - (1 - t) / (3 - V)) : ℝ) : ℂ) • A ∧
    ergotropicSpectralWidth Y = D * |3*t - V| / (V * (3 - V)) ∧
    passiveEnergy ![0, 1, 2] Y = 1 - D * |3*t - V| / (V * (3 - V)) ∧
    passiveEnergy ![0, 1, 2] (energyDephasing X) = 1 - qutritPopulationWidth X ∧
    passiveEnergy ![0, 1, 2] (energyDephasing X) - passiveEnergy ![0, 1, 2] Y =
      D * |3*t - V| / (V * (3 - V)) - qutritPopulationWidth X := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
