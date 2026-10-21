-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_topological_extension_representation
-- name    : QAlgorithms.Papers.Independent.Next46.P06.topological_extension_representation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:45:27.450821+00:00
-- url     : https://prove2.me/theorems/c98fc66f-e96f-4ffa-8cac-b72d3517735b
-- title:
--   Theorem 9.1
-- statement:
--   Let $F$ be a unital complex algebra, $E\subseteq F$ a possibly nonunital subalgebra, $\rho:E\to\mathcal L(X)$ a representation on a complex Banach space, and $A\subseteq\mathcal L(X)$ a subalgebra containing its image. Let $\tau_1,\tau_2$ be algebraic convergence relations on $F,A$ over any common index set $I$: each relation is a complex subalgebra of families paired with limits and contains every constant family. Suppose joint closability holds: $e_i\in E$, $e_i\to_{\tau_1}0$ and $\rho(e_i)\to_{\tau_2}T$ imply $T=0$. Define
--
--   $$E^\tau=\{f:\exists(e_i)\subseteq E,\ T\in A,\ e_i\to_{\tau_1}f,\ \rho(e_i)\to_{\tau_2}T\}.$$
--
--   Then $E^\tau$ is a complex subalgebra containing $E$, the assignment $\rho^\tau(f)=T$ is well defined and is an algebra homomorphism, and $\rho^\tau|_E=\rho$. Neither directedness nor a topology nor unitality of $\rho$ is assumed.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 22, Theorem 9.1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Theorem 9.1, PDF pp.22–23: the constructed map is a (possibly nonunital)
complex algebra homomorphism extending rho, under exactly the two convergence
axioms. The index type is arbitrary, including the empty type. -/
theorem topological_extension_representation [CompleteSpace X] {I : Type*}
    (rho : F → X →L[ℂ] X) (E : Set F) (hrho : AlgebraRepresentationOn rho E)
    (A : Set (X →L[ℂ] X)) (hA : SubalgebraSet A)
    (himage : ∀ e ∈ E, rho e ∈ A)
    (tau1 : (I → F) → F → Prop)
    (tau2 : (I → (X →L[ℂ] X)) → (X →L[ℂ] X) → Prop)
    (htau1 : AlgebraicConvergenceOn tau1 Set.univ)
    (htau2 : AlgebraicConvergenceOn tau2 A)
    (hclosable : JointClosable rho E tau1 tau2) :
    SubalgebraSet (topologicalDomain rho E A tau1 tau2) ∧
    E ⊆ topologicalDomain rho E A tau1 tau2 ∧
    AlgebraRepresentationOn (topologicalValue rho E A tau1 tau2) (topologicalDomain rho E A tau1 tau2) ∧
    (∀ e ∈ E, topologicalValue rho E A tau1 tau2 e = rho e) ∧
    (∀ f T, topologicalGraph rho E A tau1 tau2 f T →
      topologicalValue rho E A tau1 tau2 f = T) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
