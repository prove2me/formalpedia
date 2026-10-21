-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_ensembleEquivalence
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.ensembleEquivalence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:44:26.043958+00:00
-- url     : https://prove2.me/theorems/05f89060-70e5-4902-8f4a-3d98568f6736
-- title:
--   Theorem 3.1: equivalence of the three quantum ensembles
-- statement:
--   Let $X_k^N$ be uniformly operator-norm bounded self-adjoint observables on nonzero finite-dimensional complex Hilbert spaces, with arbitrary index set $K$. Suppose strictly positive density matrices $\sigma^N$ define normalized states $\omega^N(A)=\operatorname{Tr}(\sigma^NA)$ that converge in mean to $x\in\mathbb R^K$ and attain the mean-canonical entropy supremum $H_1^{\rm can}(x)$.
--
--   Assume that for every $k$ and $\delta>0$ there are $C_k(\delta)>0$ and $N_k(\delta)$, independent of $N$, such that $\omega^N(1_{[x_k-\delta,x_k+\delta]}(X_k^N))\ge1-e^{-C_k(\delta)N}$ for $N>N_k(\delta)$. Put $B^N=N^{-1}(\log\sigma^N-\omega^N(\log\sigma^N)I)$, and assume for every $\delta>0$ that $N^{-1}\log\omega^N(1_{[-\delta,\delta]}(B^N))\to0$, with $\log0=-\infty$. Then
--
--   $$H^{\rm mc}(x)=H^{\rm can}(x)=H_1^{\rm can}(x)\ge0.$$
--
--   The microcanonical, concentrating-canonical, and mean-canonical entropies use outer suprema over their respective sequences. Equipartition here requires subexponential spectral mass, rather than mass tending to one. This is the paper's conditional equivalence theorem.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 8, Theorem 3.1: equivalence of the three quantum ensembles

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

/-- Theorem 3.1, PDF p.8: positive definite canonical optimizer, exponential
coordinate concentration and subexponential equipartition imply full ensemble equivalence. -/
theorem ensembleEquivalence {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (rho : OperatorSequence S) (x : K → ℝ)
    (hpositive : ∀ n, (rho n).PosDef)
    (hcanonical : canonicalMacrostate S rho x)
    (hexponential : exponentiallyConcentrates S rho x)
    (hequipartition : asymptoticEquipartition rho) :
    microcanonicalEntropy S x = canonicalEntropy S x ∧
      canonicalEntropy S x = meanCanonicalEntropy S x ∧
      0 ≤ meanCanonicalEntropy S x := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
