-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P21_finiteCodewordDistinguishability
-- name    : QAlgorithms.Papers.Independent.Frontier30.P21.finiteCodewordDistinguishability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:20:50.020012+00:00
-- url     : https://prove2.me/theorems/0a6b0670-ea0e-4307-92a9-0fefd089e0ee
-- title:
--   Lossless binary discrimination of finite number and coherent words
-- statement:
--   Let $L\geq1$ be a finite word length and let $p\in(0,1)$ be the prior probability of the first of two codewords, with second prior $1-p$. On the lossless channel, take distinct occupation tuples $a,b\in\mathbb N^L$ and arbitrary finite amplitude tuples $\alpha,\beta\in\mathbb C^L$. Their product number and coherent words are normalized states in $\ell^2(\mathbb N^L;\mathbb C)$. For normalized vectors $u,v$, define the minimum binary average decoding error by minimizing
--
--   $$
--   p\bigl(1-\langle u|T|u\rangle\bigr)+(1-p)\langle v|T|v\rangle
--   $$
--
--   over all bounded effects $0\leq T\leq I$, where $T$ selects the first word. The minima are attained and satisfy
--
--   $$
--   P_{\mathrm{err}}^{\min}(|a\rangle,|b\rangle;p)=0,
--   \qquad
--   P_{\mathrm{err}}^{\min}(|\alpha\rangle,|\beta\rangle;p)>0.
--   $$
--
--   This contrasts exact finite-word distinguishability with asymptotic capacity attainment. It does not assert that every decoder is optimal or that each directed conditional error is positive.
--
--   **Formalization Note** The theorem uses an attained least element of the set of all executed binary errors, avoiding any default value of a real infimum. It also concludes that the constructed coherent words have their specified coefficients and unit norm.
-- source:
--   Classical capacity of the lossy bosonic channel: the exact solution, arXiv:quant-ph/0308012v2, PDF p. 2, Discussion, finite-length confusion

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P21

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open scoped Topology

attribute [local instance] Classical.propDecidable

/-- PDF p.2, Discussion: on the lossless channel, distinct finite number words
have zero minimum binary average error, while every pair of finite coherent
words has strictly positive minimum error. Both priors are positive. IsLeast
expresses optimal discrimination, not a claim about every receiver. -/
theorem finiteCodewordDistinguishability (L : ℕ) (hL : 0 < L)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (a b : Fin L → ℕ) (hab : a ≠ b) (alpha beta : Fin L → ℂ) :
    ‖numberWord a‖ = 1 ∧ ‖numberWord b‖ = 1 ∧
    CoherentWordRealized alpha ∧ CoherentWordRealized beta ∧
    IsLeast (binaryErrorValues p (numberWord a) (numberWord b)) 0 ∧
    ∃ e : ℝ, 0 < e ∧
      IsLeast (binaryErrorValues p (coherentWord alpha) (coherentWord beta)) e := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P21

end
