-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_hardy_success_probability
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.hardy_success_probability
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:31:58.184851+00:00
-- url     : https://prove2.me/theorems/85a138a7-a304-473b-a1ed-1df0fb40ca07
-- title:
--   Hardy success probability of the constructed state
-- statement:
--   For each party $P\in\{A,B\}$, let $\alpha_P,\beta_P\in\mathbb C$ satisfy $|\alpha_P|^2+|\beta_P|^2=1$ and $0<|\alpha_P|<1$. The unprimed measurement basis is $|0\rangle,|1\rangle$, and the primed basis is $|0'\rangle_P=\alpha_P|0\rangle+\beta_P|1\rangle$, $|1'\rangle_P=\overline{\beta_P}|0\rangle-\overline{\alpha_P}|1\rangle$. Write $|\psi_H\rangle$ for the last vector obtained by the ordered Gram–Schmidt construction (2)–(4), and $p_H(a,b\mid A,B)$ for its Born probabilities.
--
--   Order the product vectors as $\phi_0=|1'1'\rangle$, $\phi_1=|00'\rangle$, $\phi_2=|0'0\rangle$, $\phi_3=|00\rangle$, and denote their Gram–Schmidt vectors by $\phi_i'$. Then
--   $$
--   q:=p_H(00\mid00)=|\langle\psi_H|\phi_3\rangle|^2
--   =1-\sum_{i=0}^{2}|\langle\phi_i'|\phi_3\rangle|^2
--   =\frac{|\alpha_A\alpha_B|^2|\beta_A\beta_B|^2}{1-|\alpha_A\alpha_B|^2}.
--   $$
--   The denominator is strictly positive. This evaluates the success probability of the source's explicitly constructed state.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 3, II A: Hardy success probability

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- II A, PDF p.3: all equalities in the displayed Hardy success formula following (4).
Strict alpha bounds in HardyParameters exclude the zero denominator. -/
theorem hardy_success_probability (d : HardyParameters) :
    let q := hardyBehavior d (pureDensity (psiH d)) false false false false
    q = ‖inner ℂ (psiH d) (hardyPhi d 3)‖ ^ 2 ∧
    q = 1 - ∑ i : Fin 3, ‖inner ℂ (hardyGS d (Fin.castSucc i)) (hardyPhi d 3)‖ ^ 2 ∧
    q = (‖d.alpha false * d.alpha true‖ ^ 2 * ‖d.beta false * d.beta true‖ ^ 2) /
      (1 - ‖d.alpha false * d.alpha true‖ ^ 2) ∧
    0 < 1 - ‖d.alpha false * d.alpha true‖ ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
