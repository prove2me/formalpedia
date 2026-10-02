-- Prove2me | Theorems.Thm_TeschlQM_SelfAdjoint_essentiallySelfAdjoint_iff
-- name    : TeschlQM.SelfAdjoint.essentiallySelfAdjoint_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:21:41.711989+00:00
-- url     : https://prove2.me/theorems/19931eef-c8f7-49fa-8150-c1063b3be225
-- title:
--   Lemma 2.7 — criterion for essential self-adjointness
-- statement:
--   Let $A$ be a symmetric operator on a complex Hilbert space $\mathfrak{H}$. Then $A$ is essentially self-adjoint if and only if one of the following conditions holds for one $z \in \mathbb{C}\setminus\mathbb{R}$:
--   $$\overline{\operatorname{Ran}(A + z)} = \overline{\operatorname{Ran}(A + z^*)} = \mathfrak{H}, \qquad\text{or}\qquad \operatorname{Ker}(A^* + z) = \operatorname{Ker}(A^* + z^*) = \{0\}.$$
--   If $A$ is nonnegative, that is $\langle \psi, A\psi\rangle \ge 0$ for all $\psi \in \mathfrak{D}(A)$, then real $z$ may also be admitted, namely $z > 0$ (so that the spectral parameter $-z$ of $A + z = A - (-z)$ lies in $(-\infty, 0)$).
--
--   **Formalization Note.** Each of the two conditions is stated separately as equivalent to essential self-adjointness, each with an existential "for one $z$". The closure of the range is `Submodule.topologicalClosure`; $A^*$ is Mathlib's `LinearPMap.adjoint`, which is the book's adjoint because symmetric operators are densely defined. Nonnegativity is $\operatorname{Re}\langle\psi, A\psi\rangle \ge 0$ (the form is real for symmetric $A$), and the admitted $z$ are then those with $\operatorname{Im} z \ne 0$ or with $z$ real and positive. The book writes "$z \in (-\infty, 0)$" with the conditions on $A + z$; read literally that is false ($A = -d^2/dx^2$ on $C_c^\infty(0,\infty)$ is nonnegative and not essentially self-adjoint, while $\operatorname{Ker}(A^* - 1) = \{0\}$). The book's proof uses $A + \varepsilon$ with $\varepsilon > 0$, which is the version stated here.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 66, Lemma 2.7

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Definitions.Def_TeschlQM_Shared_IsEssentiallySelfAdjoint

namespace TeschlQM.SelfAdjoint

open ComplexConjugate
open scoped InnerProductSpace

/-- Teschl, Lemma 2.7 (p. 66): a symmetric `A` is essentially self-adjoint iff, for one
`z ∈ ℂ \ ℝ`, `closure(Ran(A + z)) = closure(Ran(A + z*)) = ℌ`, iff, for one `z ∈ ℂ \ ℝ`,
`Ker(A* + z) = Ker(A* + z*) = {0}`. If `A` is nonnegative (`⟨ψ, Aψ⟩ ≥ 0` on `𝔇(A)`), real `z`
may also be admitted. The book writes `z ∈ (-∞, 0)`, but its conditions are on `A + z` and its proof
uses `A + ε` with `ε > 0`; read literally the clause is false (`-d²/dx²` on `C_c^∞(0, ∞)` is
nonnegative, not essentially self-adjoint, and `Ker(A* - 1) = {0}`), so the admitted real `z` are
`z ∈ (0, ∞)` in the `A + z` convention, i.e. the spectral point `-z ∈ (-∞, 0)`. -/
theorem essentiallySelfAdjoint_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) :
    (TeschlQM.Shared.IsEssentiallySelfAdjoint A ↔
      ∃ z : ℂ, z.im ≠ 0 ∧ (rangeAdd A z).topologicalClosure = ⊤ ∧
        (rangeAdd A (conj z)).topologicalClosure = ⊤) ∧
    (TeschlQM.Shared.IsEssentiallySelfAdjoint A ↔
      ∃ z : ℂ, z.im ≠ 0 ∧ kerAdd A.adjoint z = ⊥ ∧ kerAdd A.adjoint (conj z) = ⊥) ∧
    ((∀ ψ : A.domain, 0 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) →
      (TeschlQM.Shared.IsEssentiallySelfAdjoint A ↔
        ∃ z : ℂ, (z.im ≠ 0 ∨ (z.im = 0 ∧ 0 < z.re)) ∧ (rangeAdd A z).topologicalClosure = ⊤ ∧
          (rangeAdd A (conj z)).topologicalClosure = ⊤) ∧
      (TeschlQM.Shared.IsEssentiallySelfAdjoint A ↔
        ∃ z : ℂ, (z.im ≠ 0 ∨ (z.im = 0 ∧ 0 < z.re)) ∧ kerAdd A.adjoint z = ⊥ ∧
          kerAdd A.adjoint (conj z) = ⊥)) := by sorry

end TeschlQM.SelfAdjoint
