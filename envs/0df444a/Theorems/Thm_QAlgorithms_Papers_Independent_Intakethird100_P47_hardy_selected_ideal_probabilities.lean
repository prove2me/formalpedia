-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_hardy_selected_ideal_probabilities
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.hardy_selected_ideal_probabilities
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:33:25.142333+00:00
-- url     : https://prove2.me/theorems/867146a2-8186-4b55-8585-6c933daee7b9
-- title:
--   Probabilities of the selected ideal implementation
-- statement:
--   For each party $P\in\{A,B\}$, let $\alpha_P,\beta_P\in\mathbb C$ satisfy $|\alpha_P|^2+|\beta_P|^2=1$ and $0<|\alpha_P|<1$. The unprimed measurement basis is $|0\rangle,|1\rangle$, and the primed basis is $|0'\rangle_P=\alpha_P|0\rangle+\beta_P|1\rangle$, $|1'\rangle_P=\overline{\beta_P}|0\rangle-\overline{\alpha_P}|1\rangle$. Write $|\psi_H\rangle$ for the last vector obtained by the ordered Gram–Schmidt construction (2)–(4), and $p_H(a,b\mid A,B)$ for its Born probabilities.
--
--   If $|\alpha_A|=|\alpha_B|=\sqrt{(\sqrt5-1)/2}$, the constructed behavior satisfies all four Hardy conditions, and
--   $$
--   0<p_H(00\mid00)=\frac{5\sqrt5-11}{2}<p_H(00\mid11)=\sqrt5-2.
--   $$
--   This evaluates the implementation chosen in II B and III. It does not assert that every device attaining the first value has this realization.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 3, II B / III: selected ideal implementation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- II B / III, PDF pp.3–4, (7): evaluate the selected ideal two-qubit implementation.
This is not the external optimality or arbitrary-dimension self-testing result. -/
theorem hardy_selected_ideal_probabilities (d : HardyParameters)
    (halpha : ∀ P, ‖d.alpha P‖ = Real.sqrt ((Real.sqrt 5 - 1) / 2)) :
    let p := hardyBehavior d (pureDensity (psiH d))
    HardyConditions p ∧
    p false false false false = (5 * Real.sqrt 5 - 11) / 2 ∧
    p true true false false = Real.sqrt 5 - 2 ∧
    0 < p false false false false ∧
    p false false false false < p true true false false := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
