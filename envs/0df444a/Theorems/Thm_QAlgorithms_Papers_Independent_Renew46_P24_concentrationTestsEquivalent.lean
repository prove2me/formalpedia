-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_concentrationTestsEquivalent
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.concentrationTestsEquivalent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:41:41.356038+00:00
-- url     : https://prove2.me/theorems/eba0596d-d0aa-4335-853c-288e1fb1f6c6
-- title:
--   §2.2.1: equivalent tests for concentration of states
-- statement:
--   Let $X_k^N$ be uniformly operator-norm bounded self-adjoint observables on nonzero finite-dimensional complex Hilbert spaces, with arbitrary index set $K$ and fixed radii $r_k>\sup_N\|X_k^N\|$. Let $\omega^N(A)=\operatorname{Tr}(\sigma^NA)$, where $\sigma^N$ is positive semidefinite with trace one, and let $x\in\mathbb R^K$. Then
--
--   $$\bigl[\omega^N(G(X^N))\longrightarrow G(x)\text{ for every absolutely weighted-summable ordered analytic series }G\bigr]\ \Longleftrightarrow\ \bigl[\omega^N(F(X_k^N))\longrightarrow F(x_k)\text{ for every }k\in K,\ F\in C(\mathbb R;\mathbb C)\bigr].$$
--
--   The analytic series use the weights $\prod_i r_{k_i}$ on finite words. This characterizes concentration for general mixed states; convergence of the first moments alone remains a separate, weaker notion.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 6, §2.2.1: equivalent tests for concentration of states

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

/-- PDF p.6, section 2.2.1: analytic concentration of normalized general states
is equivalent to all single-variable continuous tests; mean convergence is separate. -/
theorem concentrationTestsEquivalent {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (rho : OperatorSequence S) (x : K → ℝ)
    (hrho : IsStateSequence rho) :
    stateConcentrates S rho x ↔ singleVariableConcentrates S rho x := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
