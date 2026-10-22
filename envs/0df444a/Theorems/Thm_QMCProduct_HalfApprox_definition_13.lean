-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_definition_13
-- name    : QMCProduct.HalfApprox.definition_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:04.384518+00:00
-- url     : https://prove2.me/theorems/1ebca156-bb39-4f48-8e58-ad0cb1c7b1ce
-- title:
--   Definition 13, p. 19 — γ = 0.911 satisfies the hypotheses of Lemma 6
-- statement:
--   Let $\gamma=0.911$. Then $\gamma\in[1/3,1)$,
--   $$h(v,0.911)<0\quad\text{for every }v\in(-1/3,0.911],\qquad\text{and}\qquad\frac{1+F(3,0.911)}{1+3\cdot0.911}\ge\frac12,$$
--   with $h$ and $F(3,\cdot)$ as in Lemma 6. Hence Lemma 6 applies at this threshold.
--
--   Although the paper labels it a definition, its content is a claim: the paper fixes $\gamma:=0.911$ for the rest of its analysis "which does so". Numerically, the numerator of $h(\cdot,0.911)$ is about $-35.99$ and the ratio is about $0.50043$.
--
--   **Formalization Note** The threshold is written as the exact rational $911/1000$. The paper's choice of $\gamma$ is not encoded; the item records only the property it asserts the value has.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 19, Definition 13

import Definitions.Def_QMCProduct_HalfApprox_Algorithm

set_option autoImplicit false

namespace QMCProduct.HalfApprox

/-- Definition 13, p. 19: `γ = 0.911` satisfies the hypotheses of Lemma 6. -/
theorem definition_13 :
    (1 / 3 : ℝ) ≤ 911 / 1000 ∧ (911 / 1000 : ℝ) < 1 ∧
    (∀ v ∈ Set.Ioc (-(1 / 3 : ℝ)) (911 / 1000), hLemma6 v (911 / 1000) < 0) ∧
    (1 / 2 : ℝ) ≤ (1 + F 3 (911 / 1000)) / (1 + 3 * (911 / 1000)) := by sorry

end QMCProduct.HalfApprox
