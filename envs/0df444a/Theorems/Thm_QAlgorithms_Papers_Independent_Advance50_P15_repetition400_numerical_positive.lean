-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P15_repetition400_numerical_positive
-- name    : QAlgorithms.Papers.Independent.Advance50.P15.repetition400_numerical_positive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:26:07.613904+00:00
-- url     : https://prove2.me/theorems/35e42334-a9d9-46c1-a6a3-de6ea87e1bdf
-- title:
--   Positive 400-bit repetition expression above error rate 0.129
-- statement:
--   For a block of $m\ge1$ bits, let $P_m^b(a,s)$ be the logical-bit and individual-syndrome distribution obtained by decoding independent Bernoulli$(b)$ errors. Let $H_b(A\mid S)$ be its Shannon conditional entropy in bits. Put $\widetilde p=p(1-q)+q(1-p)$ and
--
--   $$
--   \rho_{p,q}=(1-q)|\phi_+\rangle\langle\phi_+|+q|\phi_-\rangle\langle\phi_-|,
--   \qquad |\phi_\pm\rangle=\sqrt{1-p}|0\rangle\pm\sqrt p|1\rangle.
--   $$
--
--   Writing $S$ for von Neumann entropy in bits and $Z$ for the Pauli phase operator, define the raw Eq. (2) expression per sifted signal by
--
--   $$
--   R_m(p,q)=\frac{1-H_{\widetilde p}(A\mid S)+mS(\rho_{p,q})
--   -S\!\left(\tfrac12\rho_{p,q}^{\otimes m}
--   +\tfrac12 Z^{\otimes m}\rho_{p,q}^{\otimes m}Z^{\otimes m}\right)}m.
--   $$
--
--   The paper’s numerical construction gives
--
--   $$
--   \exists\,p\in(0.129,1/2]\quad R_{400}(p,0.32)>0.
--   $$
--
--   This records the advertised improvement beyond 0.129 without asserting that the rounded 0.1292 is an exact root, maximizer, or optimal threshold. The numerical positivity is an input to the operational rate claim, whose security interface is deferred separately under the Theorem 1 node.
--
--   **Formalization Note** Conditional entropy is $H(A,S)-H(S)$, avoiding division by zero on impossible syndromes. Lean uses $k=399$ and $q=8/25$.
-- source:
--   Structured Codes Improve the Bennett-Brassard-84 Quantum Key Rate, arXiv:quant-ph/0607018v2, PDF p. 3, Numerical key rates; Figure 1 caption on PDF p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P15

open QAlgorithms

open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Smith--Renes--Smolin, PDF p.3, numerical key rates, and p.4, Figure 1:
m=400 and q=0.32 yield a positive Eq.(2) expression at a noise rate strictly
above 0.129. The rounded 0.1292 is not asserted to be an exact root or optimum.
This is the numerical assertion; operational achievement is deferred separately. -/
theorem repetition400_numerical_positive :
    ∃ p : ℝ, 129 / 1000 < p ∧ p ≤ 1 / 2 ∧
      0 < repetitionExpression 399 p (8 / 25) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P15

end
