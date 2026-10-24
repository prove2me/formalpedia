-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_microcanonicalHTheorem
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.microcanonicalHTheorem
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:48:29.399987+00:00
-- url     : https://prove2.me/theorems/c5646181-9c68-4482-8c65-273ea8b65c0e
-- title:
--   Theorem 4.1: microcanonical H-theorem
-- statement:
--   Let $X_k^N$ be a uniformly bounded self-adjoint family on nonzero finite-dimensional complex Hilbert spaces, and let $H^{\rm mc}$ be its extended-real microcanonical entropy. Put $\Omega=\{x:H^{\rm mc}(x)\ge0\}$. Suppose complex-linear unital star automorphisms $\tau_{t,s}^N$ satisfy $\tau_{t,s}^N=\tau_{t,u}^N\circ\tau_{u,s}^N$ for $t\ge u\ge s\ge0$. Let $\varphi_{t,s}:\Omega\to\Omega$ satisfy $\varphi_{t,u}\circ\varphi_{u,s}=\varphi_{t,s}$.
--
--   Assume that for every $x\in\Omega$ there is one microcanonical maximizing projection sequence $P^N(x)$ such that, for every absolutely weighted-summable ordered analytic test $G$ and every $t\ge s\ge0$, $\operatorname{tr}(\tau_{t,s}^NG(X^N)\mid P^N(x))\to G(\varphi_{t,s}x)$. Then
--
--   $$H^{\rm mc}(\varphi_{s,0}x)\le H^{\rm mc}(\varphi_{t,0}x)\qquad(x\in\Omega,\ 0\le s\le t).$$
--
--   The maximizing sequence is chosen before all tests and times. This is nonstrict entropy monotonicity under macroscopic autonomy.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 12, Theorem 4.1: microcanonical H-theorem

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

/-- Theorem 4.1, PDF p.12: microcanonical entropy is nondecreasing on every
macroscopic trajectory under autonomy and the macroscopic semigroup law. -/
theorem microcanonicalHTheorem {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (tau : AutomorphismDynamics S)
    (htau : AutomorphismCocycle tau) (phi : MacroscopicDynamics K)
    (hautonomy : microcanonicalAutonomy S tau phi)
    (hsemigroup : macroscopicSemigroup (microcanonicalAdmissible S) phi) :
    ∀ x, microcanonicalAdmissible S x →
      MonotoneOn (fun t => microcanonicalEntropy S (phi t 0 x)) (Set.Ici 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
