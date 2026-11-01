-- Prove2me | Theorems.Thm_WildeQIT_Gentle_theorem_9_2_1
-- name    : WildeQIT.Gentle.theorem_9_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:33.919741+00:00
-- url     : https://prove2.me/theorems/677c292e-ae3c-4479-84db-a9345ba85b5c
-- title:
--   Theorem 9.2.1 (Uhlmann): $\max_U|\langle\varphi^\rho|U_R\otimes I_A|\varphi^\sigma\rangle|^2=\|\sqrt\rho\sqrt\sigma\|_1^2$
-- statement:
--   Let $\rho_A,\sigma_A$ be density operators on a finite-dimensional system $A$, and let $|\varphi^\rho\rangle_{RA}$, $|\varphi^\sigma\rangle_{RA}$ be purifications of $\rho_A$ and $\sigma_A$ on a common finite-dimensional reference system $R$. Then the maximum, over all unitaries $U_R$ on $R$, of the squared overlap of the purifications exists and equals the squared trace norm of $\sqrt{\rho_A}\sqrt{\sigma_A}$:
--
--   $$F(\rho_A,\sigma_A)=\max_{U}\bigl|\langle\varphi^\rho|_{RA}\,U_R\otimes I_A\,|\varphi^\sigma\rangle_{RA}\bigr|^2=\bigl\|\sqrt{\rho_A}\sqrt{\sigma_A}\bigr\|_1^2 .$$
--
--   The theorem identifies the Uhlmann fidelity (Definition 9.2.3), a maximal overlap of purifications, with the closed formula used in every later fidelity computation of the chapter.
--
--   **Formalization Note** The maximum is stated as `IsGreatest`: some unitary attains the value $\|\sqrt\rho\sqrt\sigma\|_1^2$, and no unitary exceeds it. $U_R\otimes I_A$ is the Kronecker product on the index type $r\times a$; $\|\cdot\|_1$ is the published `WildeQIT.traceNorm` and $\sqrt\cdot$ is `CFC.sqrt`. The squared quantity $\|\sqrt\rho\sqrt\sigma\|_1^2$ is the published `WildeQIT.fidelity`. The platform theorem `Claimed50.P12.lemmaB_3` (Proved) states the root-fidelity form with a supremum and does not assert that it is attained.
--
--   Differences from the source:
--   - generalization: reference system $R$ with $\dim R=\dim A$ ("for now", p. 265) → any finite reference system $R$; reason: the book's case is the instance $R=A$, and the identity holds for purifications on any common $R$.
--   - encoding: "particular respective purifications" $|\varphi^\rho\rangle,|\varphi^\sigma\rangle$ → arbitrary purifications, universally quantified; reason: the book fixes them without further condition.
--   - encoding: $\max_U$ → `IsGreatest` of the set of overlap values; reason: the same claim (the maximum exists and has this value).
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 9.2.1 (Uhlmann's Theorem), eq. (9.102), p. 265; Definition 9.2.3, eq. (9.100), p. 265

import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_Gentle_IsPurification
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup

open Matrix
open Kronecker
open scoped MatrixOrder

namespace WildeQIT.Gentle

/-- **Theorem 9.2.1 (Uhlmann's Theorem)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 265, eq. (9.102)). Let `ρ_A, σ_A` be density operators and let
`|φ^ρ⟩_{RA}`, `|φ^σ⟩_{RA}` be purifications of them on a common reference system `R`. Then the
maximum over unitaries `U_R` of `|⟨φ^ρ|_{RA} (U_R ⊗ I_A) |φ^σ⟩_{RA}|²` exists and equals
`‖√ρ_A √σ_A‖₁²`.

**Formalization Note.** Finite dimensions throughout (matrices over finite index types). The
maximum is stated as `IsGreatest` (attained by some unitary, and an upper bound for all of them).
`R` is any finite reference system; the book's §9.2.3 takes `dim R = dim A` "for now", which is the
instance `r = a`. `U ⊗ I` is the Kronecker product `U ⊗ₖ 1` on the index `r × a`; the overlap
`⟨ψ|v⟩` is `star ψ ⬝ᵥ v`; `‖·‖₁` is the published `WildeQIT.traceNorm` and `√·` is `CFC.sqrt`.
The book's fidelity `F(ρ, σ) = ‖√ρ √σ‖₁²` is the published `WildeQIT.fidelity`. -/
theorem theorem_9_2_1 {a r : Type} [Fintype a] [DecidableEq a] [Fintype r] [DecidableEq r]
    (ρ σ : Matrix a a ℂ) (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (φρ φσ : r × a → ℂ) (hφρ : IsPurification φρ ρ) (hφσ : IsPurification φσ σ) :
    IsGreatest {x : ℝ | ∃ U ∈ Matrix.unitaryGroup r ℂ,
        x = ‖star φρ ⬝ᵥ (((U : Matrix r r ℂ) ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ φσ)‖ ^ 2}
      (traceNorm (CFC.sqrt ρ * CFC.sqrt σ) ^ 2) := by sorry

end WildeQIT.Gentle
