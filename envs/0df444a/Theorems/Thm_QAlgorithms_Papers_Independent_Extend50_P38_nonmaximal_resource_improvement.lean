-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P38_nonmaximal_resource_improvement
-- name    : QAlgorithms.Papers.Independent.Extend50.P38.nonmaximal_resource_improvement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:56:26.699739+00:00
-- url     : https://prove2.me/theorems/4e8a038a-6aa4-443e-92e6-63c5c9f1cda6
-- title:
--   Exact two-port witness that a nonmaximal resource improves fidelity
-- statement:
--   For two qubit ports ($N=d=2$), there is a separable pure resource of the form $|0\rangle_A^{\otimes2}\otimes|e_1e_2\rangle_B$, where $|e_1\rangle,|e_2\rangle$ are orthogonal, and a two-outcome POVM attaining
--
--   $$F_{\rm sep}=\frac12,\qquad f_{\rm sep}=\frac23.$$
--
--   The resource is not maximally entangled across Alice and Bob. In contrast, for every resource maximally entangled across those two four-dimensional registers and every two-outcome POVM,
--
--   $$f_{\rm max}\leq\frac{6+\sqrt3}{12}<\frac23.$$
--
--   Thus a nonmaximal resource strictly improves fidelity over maximally entangled resources in an exact instance. The comparison uses the exact qubit SRM formula and its optimality, rather than an uncertified numerical optimum.
-- source:
--   Asymptotic teleportation scheme as a universal programmable quantum processor, arXiv:0807.4568v2, PDF p. 4, Unnumbered resource-improvement observation; analytic N=d=2 specialization

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P38

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions; neither is re-declared in this module.

open QAlgorithms.Papers.Independent.Frontier18.P14 (singlet)

open QAlgorithms.Papers.Independent.Renew46.P01 (SpinPath)

/-- PDF p.4: the nonmaximal-resource improvement, pinned analytically to N=d=2.
The source's separable attaining resource has F=1/2, f=2/3; all measurements on two
singlets, equivalently any maximally entangled resource, have f≤(6+sqrt(3))/12<2/3. No unverified numerical optimum is used. -/
theorem nonmaximal_resource_improvement :
    ∃ e : Fin 2 ↪ Fin 2,
      ValidResource (separableOperator (by decide : 0 < 2) e) ∧
      (¬ ∃ c : ℝ, separableOperator (by decide : 0 < 2) e *
        (separableOperator (by decide : 0 < 2) e)ᴴ =
          (c : ℂ) • (1 : Matrix (Ports 2 2) (Ports 2 2) ℂ)) ∧
      ∃ M : Fin 2 → Matrix (AC 2 2) (AC 2 2) ℂ, IsPOVM M ∧
        QuditFidelity.entanglementFidelity 2 (by decide)
          (teleport (separableOperator (by decide) e) M) = 1 / 2 ∧
        QuditFidelity.averageFidelity 2 (by decide)
          (teleport (separableOperator (by decide) e) M) = 2 / 3 ∧
        (∀ O : Matrix (Ports 2 2) (Ports 2 2) ℂ, O * Oᴴ = 1 →
          ∀ P : Fin 2 → Matrix (AC 2 2) (AC 2 2) ℂ, IsPOVM P →
          QuditFidelity.averageFidelity 2 (by decide) (teleport O P) ≤
            (6 + Real.sqrt 3) / 12) ∧
        (6 + Real.sqrt 3) / 12 < (2 / 3 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P38

end
