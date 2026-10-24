-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_product_fidelity
-- name    : QAlgorithms.Papers.Independent.Support50.P02.product_fidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:11:06.192672+00:00
-- url     : https://prove2.me/theorems/0099237c-028f-4615-a8d3-6f174575d09e
-- title:
--   Lemma 2: product fidelity from a near-pure marginal
-- statement:
--   Let $A,B$ be finite, positive-dimensional complex registers, $\phi^A$ a unit vector, $\rho^B$ a density operator, and $\Omega^{AB}$ a density operator. Define its marginals by $\Omega^A=\operatorname{Tr}_B\Omega$ and $\Omega^B=\operatorname{Tr}_A\Omega$. Let $\epsilon\in\mathbb R$ satisfy $F(\phi,\Omega^A)\ge1-\epsilon$, where $F$ is squared Uhlmann fidelity. Then
--   $$F(\phi\otimes\rho,\Omega)\ge1-\|\rho-\Omega^B\|_1-3\epsilon.$$
--   The trace norm is not halved. This relates a near-pure marginal to a joint product target. No positive-overlap assumption is imposed; the zero-overlap case is included.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 10, Lemma 2: product fidelity from a near-pure marginal

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P02

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Support50.P02

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E R S I J : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]

variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Lemma 2, PDF pp.10–11: both marginals are computed from Omega.
No f>0 hypothesis is imposed: the zero-overlap case is part of the theorem.
The proof's claim of general fidelity linearity is not used as a definition. -/
theorem product_fidelity [Nonempty A] [Nonempty B]
    (phi : EuclideanSpace ℂ A) (hp : IsState phi)
    (rho : Op B) (hr : IsDensityMatrix rho) (Omega : Op (A × B))
    (hO : IsDensityMatrix Omega) (epsilon : ℝ)
    (hf : 1 - epsilon ≤ squaredFidelity (pureDensity phi) (traceRight Omega)) :
    1 - traceNorm (rho - traceLeft Omega) - 3 * epsilon ≤
      squaredFidelity (Matrix.kronecker (pureDensity phi) rho) Omega := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
