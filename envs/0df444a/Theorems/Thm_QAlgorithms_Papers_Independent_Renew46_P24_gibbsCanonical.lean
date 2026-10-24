-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_gibbsCanonical
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.gibbsCanonical
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:42:40.364561+00:00
-- url     : https://prove2.me/theorems/946d2949-0047-4efc-82f8-224e9ef18817
-- title:
--   §2.2.3: Gibbs families attain the mean-canonical entropy
-- statement:
--   Let $X_1^N,\ldots,X_q^N$ be uniformly bounded self-adjoint observables on nonzero finite-dimensional complex Hilbert spaces. Fix real coefficients $\lambda=(\lambda_1,\ldots,\lambda_q)$ independently of $N$, and define
--
--   $$Z_\lambda^N=\operatorname{Tr}\exp\!\left(N\sum_k\lambda_kX_k^N\right),\qquad \sigma_\lambda^N=(Z_\lambda^N)^{-1}\exp\!\left(N\sum_k\lambda_kX_k^N\right).$$
--
--   Suppose $\operatorname{Tr}(\sigma_\lambda^NX_k^N)\to x_k$ for every $k$. Let $S(\sigma)=-\operatorname{Tr}(\sigma\log\sigma)$, and let $H_1^{\rm can}(x)$ be the supremum of $\limsup_N S(\sigma^N)/N$ over all normalized state sequences with these mean limits. Then the constructed Gibbs family attains this supremum, and
--
--   $$H_1^{\rm can}(x)=\limsup_{N\to\infty}\frac{S(\sigma_\lambda^N)}N=\limsup_{N\to\infty}\frac{\log Z_\lambda^N}{N}-\sum_k\lambda_kx_k.$$
--
--   This supplies mean-canonical optimality as a conclusion. It does not assert microcanonical equivalence.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 7, §2.2.3: Gibbs families attain the mean-canonical entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P24

open Filter

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

-- Exact primitives verified against the pinned accepted-library SHA256 catalogue.

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, (2.14)-(2.15): a fixed real PLUS-sign Gibbs family with the stated
mean limit is an entropy optimizer, and its entropy equals pressure limsup minus lambda.x. -/
theorem gibbsCanonical {q : ℕ} (S : MacroscopicSystem (Fin q))
    (hS : IsMacroscopic S) (lambda : Fin q → ℝ) (x : Fin q → ℝ)
    (hx : meanConcentrates S (gibbsFamily S lambda) x) :
    canonicalMacrostate S (gibbsFamily S lambda) x ∧
    meanCanonicalEntropy S x =
      Filter.limsup (fun n => (pressureSequence S lambda n : EReal)) atTop -
        ((∑ k, lambda k * x k : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
