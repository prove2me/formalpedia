-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_canonicalRelativeHTheorem
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.canonicalRelativeHTheorem
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:50:06.902822+00:00
-- url     : https://prove2.me/theorems/0c0dbad8-dee2-4a83-ae8d-2c0c024138e6
-- title:
--   Theorem 4.2: canonical relative-entropy H-theorem
-- statement:
--   Let $X_k^N$ be uniformly bounded self-adjoint observables and let $\rho^N$ be normalized reference states on nonzero finite-dimensional complex Hilbert spaces. Define
--
--   $$H_1^{\rm can}(x\mid\rho)=\inf_{\omega^N\to_1x}\liminf_{N\to\infty}\frac{D(\omega^N\|\rho^N)}N,$$
--
--   where the infimum runs over normalized sequences converging in mean to $x$, and relative entropy is $+\infty$ on support failure. Put $\Omega_1(\rho)=\{x:H_1^{\rm can}(x\mid\rho)<+\infty\}$. Let unital completely positive Heisenberg maps $\tau_{t,s}^N$ obey the printed cocycle law and leave $\rho^N$ invariant. Suppose the macroscopic maps obey the semigroup law, and for each $x\in\Omega_1(\rho)$ there is one relative-entropy minimizing mean-concentrating sequence $\omega^N$ with $\omega^N(\tau_{t,s}^NX_k^N)\to(\varphi_{t,s}x)_k$ for every coordinate and interval. Then
--
--   $$H_1^{\rm can}(\varphi_{t,0}x\mid\rho)\le H_1^{\rm can}(\varphi_{s,0}x\mid\rho)\qquad(0\le s\le t).$$
--
--   The reference need not be faithful. Relative canonical optimality is minimization, and the monotonicity direction is opposite to the counting-entropy H-theorem.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 13, Theorem 4.2: canonical relative-entropy H-theorem

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

/-- Theorem 4.2, PDF p.13: relative mean-canonical entropy is nonincreasing.
Reference states may be singular; relative macrostate means minimizer of (2.12). -/
theorem canonicalRelativeHTheorem {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (reference : OperatorSequence S)
    (hreference : IsStateSequence reference) (tau : LinearDynamics S)
    (htau : StationaryCPCocycle reference tau) (phi : MacroscopicDynamics K)
    (hautonomy : meanAutonomy S reference tau phi)
    (hsemigroup : macroscopicSemigroup (RelativeAdmissible S reference) phi) :
    ∀ x, RelativeAdmissible S reference x →
      AntitoneOn (fun t => relativeCanonicalEntropy S reference (phi t 0 x))
        (Set.Ici 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
