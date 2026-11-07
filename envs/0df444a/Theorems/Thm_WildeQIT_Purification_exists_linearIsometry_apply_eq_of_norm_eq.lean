-- Prove2me | Theorems.Thm_WildeQIT_Purification_exists_linearIsometry_apply_eq_of_norm_eq
-- name    : WildeQIT.Purification.exists_linearIsometry_apply_eq_of_norm_eq
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T19:24:18.571168+00:00
-- url     : https://prove2.me/theorems/34af4286-cc77-4ae5-bf0f-9286c94ef837
-- title:
--   Linear maps with equal norms differ by an isometry of the codomain
-- statement:
--   Let $E$ be a module over $\mathbb K\in\{\mathbb R,\mathbb C\}$, let $F$ be a finite-dimensional inner product space over $\mathbb K$, and let $f,g:E\to F$ be linear maps with $\|f(v)\|=\|g(v)\|$ for every $v\in E$. Then there is a linear isometry $T:F\to F$ with $T(g(v))=f(v)$ for every $v\in E$. (The rule $g(v)\mapsto f(v)$ is a well-defined linear isometry $\operatorname{range} g\to F$, because $\ker g=\ker f$, and every linear isometry from a subspace of a finite-dimensional inner product space into it extends to the whole space.)
-- source:
--   Nielsen and Chuang, Quantum Computation and Quantum Information, Theorem 2.6 (unitary freedom in the ensemble for density matrices) (key step of the proof); Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 5.1.1 and Corollary 5.1.1, pp. 185-186

import Mathlib

namespace WildeQIT.Purification

open Matrix

/-- **Codomain isometry from equal norms.** Let `f g : E →ₗ[𝕜] F` be linear maps from a
`𝕜`-module `E` into a finite-dimensional inner product space `F` with `‖f v‖ = ‖g v‖` for every
`v`. Then there is a linear isometry `T : F →ₗᵢ[𝕜] F` with `T (g v) = f v` for every `v`.
(The map `g v ↦ f v` is a well-defined isometry `range g → F`, since `ker g = ker f`; it extends
to all of `F` because `F` is finite-dimensional.) -/
theorem exists_linearIsometry_apply_eq_of_norm_eq {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (f g : E →ₗ[𝕜] F) (h : ∀ v, ‖f v‖ = ‖g v‖) :
    ∃ T : F →ₗᵢ[𝕜] F, ∀ v, T (g v) = f v := by sorry

end WildeQIT.Purification
