-- Prove2me | Theorems.Thm_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq
-- name    : Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/53e64db4-380b-56ec-9b36-001a649c32d8
-- title:
--   Subspaces fixed pointwise by a compact operator are finite-dimensional
-- statement:
--   Let $\Bbbk$ be a nontrivially normed field that is complete, let $E$ be a normed additive commutative group equipped with the structure of a normed $\Bbbk$-vector space, and let $T : E \to E$ be a continuous $\Bbbk$-linear map which is a compact operator, i.e. satisfies `IsCompactOperator T`: some neighbourhood of $0$ in $E$ has image under $T$ contained in a compact subset of $E$. Let $V$ be a $\Bbbk$-submodule of $E$ such that $T v = v$ for every $v \in V$. The conclusion is that $V$, viewed as a $\Bbbk$-module via its coercion to a type, is finite-dimensional over $\Bbbk$. Note that $V$ is an arbitrary submodule: no closedness hypothesis is imposed on it, and no completeness hypothesis is imposed on $E$.
--
--   This is Riesz's finiteness theorem in the form usually applied to automorphic forms: a compact operator acting as the identity on a subspace forces that subspace to be finite-dimensional (equivalently, a compact idempotent has finite rank). It is used in the proof of [`AutomorphicForm.CuspidalSpectrum.exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul), where a compact convolution operator acting by the identity on a space of cusp forms yields finite-dimensionality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Topology

theorem Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (V : Submodule 𝕜 E) (hV : ∀ v ∈ V, T v = v) :
    FiniteDimensional 𝕜 ↥V := by sorry
