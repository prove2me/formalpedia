-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P53_eve_spectrum
-- name    : QAlgorithms.Papers.Independent.Intake100.P53.eve_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:47:57.780197+00:00
-- url     : https://prove2.me/theorems/cd0073ea-327b-4715-b888-fb71c7a4b32b
-- title:
--   §VII, (36)–(44): spectrum of the four-state Eve mixture
-- statement:
--   Consider the independent product construction of (36)–(41). Put $p=|c_0|^2$ and $q=|c_+|^2$, with $1/2\le p,q\le1$, and let $0\le e\le1/2$. Choose the equivalent nonnegative coefficient representatives $v_0=(\sqrt p,\sqrt{1-p})$, $v_1=(\sqrt p,-\sqrt{1-p})$, $v_+=(\sqrt q,\sqrt{1-q})$, and $v_-=(\sqrt q,-\sqrt{1-q})$. Write $D_{ij}=|v_i\otimes v_j\rangle\langle v_i\otimes v_j|$, identifying Bob's indices $0,1$ with $+,-$, respectively. Define $\rho=((1-e)(D_{00}+D_{11})+e(D_{01}+D_{10}))/2$. Entropies are in bits, with $0\log_2 0=0$. This is an algebraic construction; no identification with the disputed physical exponents (35) is assumed.
--
--   Set $s=p(1-q)+(1-p)q$, $t=pq+(1-p)(1-q)$ and $d=16e(1-e)p(1-p)q(1-q)$. The constructed $\rho$ is a density matrix. Its eigenvalues, with algebraic multiplicities, are
--
--   $$\lambda_{1,2}=\frac{s\pm\sqrt{s^2-d}}2,\qquad\lambda_{3,4}=\frac{t\pm\sqrt{t^2-d}}2.$$
--
--   All four values are nonnegative, sum to one, and $S(\rho)=-\sum_{k=1}^4\lambda_k\log_2\lambda_k$. The characteristic polynomial is the product of the four corresponding linear factors, so degenerate and zero eigenvalues are retained. This evaluates the four-state mixture's entropy without invoking the disputed physical Gram identification.
-- source:
--   Security of coherent state quantum cryptography in the presence of Gaussian noise, arXiv:quant-ph/0608015v4, PDF p. 7, §VII, (36)–(44): spectrum of the four-state Eve mixture

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P53

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39

open scoped ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.7--8, (42)--(44): spectrum and entropy of the constructed matrix,
including multiplicities and zeros. This does not identify a physical Gaussian
Gram matrix. Density is concluded before the entropy functional is interpreted. -/
theorem eve_spectrum (M : BinaryProductModel) :
    QAlgorithms.IsDensityMatrix (productMixture M) ∧
    (productMixture M).charpoly =
      ∏ k : Fin 4, (Polynomial.X - Polynomial.C (mixtureSpectrum M k : ℂ)) ∧
    (∀ k, 0 ≤ mixtureSpectrum M k) ∧ (∑ k, mixtureSpectrum M k) = 1 ∧
    QAlgorithms.vnEntropy (productMixture M) =
      -(∑ k : Fin 4, mixtureSpectrum M k * Real.logb 2 (mixtureSpectrum M k)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P53

end
