-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P25_strongContinuity_iff_quadraticContinuity
-- name    : QAlgorithms.Papers.Independent.Next46.P25.strongContinuity_iff_quadraticContinuity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:01:48.809121+00:00
-- url     : https://prove2.me/theorems/2e29f648-172f-42f3-9d98-560c56a3edf6
-- title:
--   Strong continuity of star representations is equivalent to quadratic continuity
-- statement:
--   Let $\mathfrak g$ be a real Fréchet Lie algebra with continuous bracket and let $V$ be a complex pre-Hilbert space with its norm topology, without a completeness assumption. Let $\rho:\mathfrak g\to\operatorname{End}_{\mathbb C}(V)$ be a real-linear bracket-preserving representation by skew-symmetric operators. With the source's scalar product linear in its first argument, put $q_v(x)=\langle\rho(x)^2v,v\rangle\in\mathbb R$. Then
--
--   $$
--   \rho\text{ is strongly continuous}\quad\Longleftrightarrow\quad
--   q_v\text{ is continuous for every }v\in V.
--   $$
--
--   Here $q_v(x)=-\|\rho(x)v\|^2$. Lean writes the real part of $\operatorname{inner}_{\mathbb C}(v,\rho(x)^2v)$, reversing the source's scalar-product slots. All vectors, including zero, are allowed. This is a continuity criterion on a possibly incomplete invariant domain.
-- source:
--   On Analytic Vectors for Unitary Representations of Infinite Dimensional Lie Groups, arXiv:1002.4792v2, PDF p. 16, Lemma 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P25

noncomputable section

open Set Filter Topology

open scoped Classical ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P25

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Lemma 4.5, PDF p.16: skew symmetry on a complex pre-Hilbert
    space. The source's linear-first scalar product becomes inner v (rho^2 v),
    whose real value is NEGATIVE the squared norm of rho v. -/
theorem strongContinuity_iff_quadraticContinuity
    {g : Type u} [LieRing g] [LieAlgebra ℝ g] [UniformSpace g]
    [IsUniformAddGroup g] [T2Space g] [ContinuousSMul ℝ g]
    [LocallyConvexSpace ℝ g] [TopologicalSpace.MetrizableSpace g] [CompleteSpace g]
    {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    (hBracket : Continuous (fun xy : g × g => ⁅xy.1, xy.2⁆))
    (rho : g →ₗ⁅ℝ⁆ Module.End ℂ V)
    (hSkew : ∀ (x : g) (v w : V),
      inner ℂ w (rho x v) = -inner ℂ (rho x w) v) :
    StronglyContinuous (fun x v => rho x v) ↔
      ∀ v : V, Continuous (fun x : g => (inner ℂ v (rho x (rho x v))).re) := by sorry

end QAlgorithms.Papers.Independent.Next46.P25

end
