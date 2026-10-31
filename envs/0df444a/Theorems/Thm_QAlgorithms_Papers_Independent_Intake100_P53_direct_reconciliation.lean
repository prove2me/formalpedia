-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P53_direct_reconciliation
-- name    : QAlgorithms.Papers.Independent.Intake100.P53.direct_reconciliation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:48:34.541491+00:00
-- url     : https://prove2.me/theorems/08c38a5e-cdfc-4843-b95b-10266d9e6e50
-- title:
--   §VII A, (45)–(49): direct-reconciliation entropy and Holevo formula
-- statement:
--   Consider the independent product construction of (36)–(41). Put $p=|c_0|^2$ and $q=|c_+|^2$, with $1/2\le p,q\le1$, and let $0\le e\le1/2$. Choose the equivalent nonnegative coefficient representatives $v_0=(\sqrt p,\sqrt{1-p})$, $v_1=(\sqrt p,-\sqrt{1-p})$, $v_+=(\sqrt q,\sqrt{1-q})$, and $v_-=(\sqrt q,-\sqrt{1-q})$. Write $D_{ij}=|v_i\otimes v_j\rangle\langle v_i\otimes v_j|$, identifying Bob's indices $0,1$ with $+,-$, respectively. Define $\rho=((1-e)(D_{00}+D_{11})+e(D_{01}+D_{10}))/2$. Entropies are in bits, with $0\log_2 0=0$. This is an algebraic construction; no identification with the disputed physical exponents (35) is assumed.
--
--   Construct $\rho_i=(1-e)D_{ii}+eD_{i,1-i}$ for $i=0,1$ and $\chi_{\rm DR}=S(\rho)-(S(\rho_0)+S(\rho_1))/2$. The two conditional states are density matrices and there is a unitary $U$ with $\rho_0=U\rho_1U^\dagger$. Both have spectrum, including zeros,
--
--   $$\left\{0,0,\frac{1+\sqrt{1-16e(1-e)q(1-q)}}2,\frac{1-\sqrt{1-16e(1-e)q(1-q)}}2\right\}.$$
--
--   Their entropies agree and equal the negative sum of $\lambda\log_2\lambda$ over the last two values. Consequently $\chi_{\rm DR}=S(\rho)-S(\rho_0)$. This is the direct-reconciliation entropy computation for the product construction, without a claim about physical Gaussian key extraction.
-- source:
--   Security of coherent state quantum cryptography in the presence of Gaussian noise, arXiv:quant-ph/0608015v4, PDF p. 7, §VII A, (45)–(49): direct-reconciliation entropy and Holevo formula

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P53

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39

open scoped ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.7--8, VII A, (45)--(49): unitary equivalence, both zero roots,
conditional entropy and DR Holevo formula for the product construction. -/
theorem direct_reconciliation (M : BinaryProductModel) :
    (∀ i, QAlgorithms.IsDensityMatrix (productDR M i)) ∧
    (∃ U : Matrix.unitaryGroup (Bool × Bool) ℂ,
      productDR M false = (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) *
        productDR M true * (U : Matrix (Bool × Bool) (Bool × Bool) ℂ).conjTranspose) ∧
    (∀ i, (productDR M i).charpoly = Polynomial.X ^ 2 *
      ∏ k : Fin 2, (Polynomial.X - Polynomial.C (conditionalSpectrum M.q M.e k : ℂ))) ∧
    QAlgorithms.vnEntropy (productDR M false) = QAlgorithms.vnEntropy (productDR M true) ∧
    QAlgorithms.vnEntropy (productDR M false) =
      -(∑ k : Fin 2, conditionalSpectrum M.q M.e k * Real.logb 2 (conditionalSpectrum M.q M.e k)) ∧
    productHolevoDR M = QAlgorithms.vnEntropy (productMixture M) -
      QAlgorithms.vnEntropy (productDR M false) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P53

end
