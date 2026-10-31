-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P53_reverse_reconciliation
-- name    : QAlgorithms.Papers.Independent.Intake100.P53.reverse_reconciliation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:49:26.62246+00:00
-- url     : https://prove2.me/theorems/bda55043-5058-4d73-9db1-1c90dbe61cfc
-- title:
--   §VII B, (50)–(53): reverse-reconciliation entropy and Holevo formula
-- statement:
--   Consider the independent product construction of (36)–(41). Put $p=|c_0|^2$ and $q=|c_+|^2$, with $1/2\le p,q\le1$, and let $0\le e\le1/2$. Choose the equivalent nonnegative coefficient representatives $v_0=(\sqrt p,\sqrt{1-p})$, $v_1=(\sqrt p,-\sqrt{1-p})$, $v_+=(\sqrt q,\sqrt{1-q})$, and $v_-=(\sqrt q,-\sqrt{1-q})$. Write $D_{ij}=|v_i\otimes v_j\rangle\langle v_i\otimes v_j|$, identifying Bob's indices $0,1$ with $+,-$, respectively. Define $\rho=((1-e)(D_{00}+D_{11})+e(D_{01}+D_{10}))/2$. Entropies are in bits, with $0\log_2 0=0$. This is an algebraic construction; no identification with the disputed physical exponents (35) is assumed.
--
--   Construct $\rho_{j\,{\rm(Bob)}}=(1-e)D_{jj}+eD_{1-j,j}$ for $j=0,1$, written as $\rho_+,\rho_-$. Define $\chi_{\rm RR}=S(\rho)-(S(\rho_+)+S(\rho_-))/2$. The two conditional states are density matrices and are unitarily equivalent. Both have spectrum, including zeros,
--
--   $$\left\{0,0,\frac{1+\sqrt{1-16e(1-e)p(1-p)}}2,\frac{1-\sqrt{1-16e(1-e)p(1-p)}}2\right\}.$$
--
--   Their common entropy is the negative sum of $\lambda\log_2\lambda$ over the last two values, and $\chi_{\rm RR}=S(\rho)-S(\rho_+)$. Keeping the same factor order differs from (50) only by a tensor swap. Construction from (38)–(39),(50) corrects (51)'s repeated $|c_+|^2$ to $|c_-|^2$ in the lower-right entry of the pure factor; the equivalence sentence's second $\epsilon_+$ is $\epsilon_-$. Both corrections are explicitly pending independent moderation.
-- source:
--   Security of coherent state quantum cryptography in the presence of Gaussian noise, arXiv:quant-ph/0608015v4, PDF p. 8, §VII B, (50)–(53): reverse-reconciliation entropy and Holevo formula

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P53

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39

open scoped ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.8, VII B, (50)--(53): reverse conditional spectrum and Holevo formula.
Printed epsilon_+,epsilon_+ means epsilon_+,epsilon_-. In (51), the lower-right
|c+|² of the first pure factor must be |c-|², as constructed from (38)--(39),(50).
Both source corrections require independent moderation; no physical exponents
are repaired or silently assumed here. -/
theorem reverse_reconciliation (M : BinaryProductModel) :
    (∀ j, QAlgorithms.IsDensityMatrix (productRR M j)) ∧
    (∃ U : Matrix.unitaryGroup (Bool × Bool) ℂ,
      productRR M false = (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        productRR M true * (U : Matrix (Bool × Bool) (Bool × Bool) ℂ).conjTranspose) ∧
    (∀ j, (productRR M j).charpoly = Polynomial.X ^ 2 *
      ∏ k : Fin 2, (Polynomial.X - Polynomial.C (conditionalSpectrum M.p M.e k : ℂ))) ∧
    QAlgorithms.vnEntropy (productRR M false) = QAlgorithms.vnEntropy (productRR M true) ∧
    QAlgorithms.vnEntropy (productRR M false) =
      -(∑ k : Fin 2, conditionalSpectrum M.p M.e k * Real.logb 2 (conditionalSpectrum M.p M.e k)) ∧
    productHolevoRR M = QAlgorithms.vnEntropy (productMixture M) -
      QAlgorithms.vnEntropy (productRR M false) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P53

end
