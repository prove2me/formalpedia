-- Prove2me | Theorems.Thm_ScutaruFid_reduction_to_thermal
-- name    : ScutaruFid.reduction_to_thermal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:44.42616+00:00
-- url     : https://prove2.me/theorems/87a70faf-eb5d-47a4-b29f-efed383b7521
-- title:
--   p.2, after (13): by F4 one may take $\rho_1$ thermal (undisplaced and unsqueezed)
-- statement:
--   Let $A_1,A_2$ be real symmetric positive definite $2\times2$ matrices with $\det A_j\ge1$ and $u_1,u_2\in\mathbb R^2$. There exist a unitary operator $U$ on $L^2(\mathbb R)$ and a real $2\times2$ matrix $S$ with
--
--   $$
--   \det S=1,\qquad SA_1S^{\mathsf T}=\sqrt{\det A_1}\,I,
--   $$
--
--   such that, whenever $\rho_j$ is the operator with kernel `stateKernel A_j u_j`,
--
--   1. $U\rho_1U^*$ is the undisplaced, unsqueezed state with matrix $\sqrt{\det A_1}\,I$ and mean $0$, and
--   2. $U\rho_2U^*$ is the Gaussian state with matrix $SA_2S^{\mathsf T}$ and mean $S(u_2-u_1)$.
--
--   Combined with F4, it reduces the fidelity of two arbitrary Gaussian states to the case "$\rho_1$ thermal, $\rho_2$ displaced squeezed thermal" in which the paper computes (17).
--
--   Differences from the source:
--   - reading: it suffices to consider that ρ1 is a thermal state and only ρ2 is a displaced squeezed thermal state → a unitary U and S with det S = 1 carry (A₁, u₁) to (√(det A₁) I, 0) and (A₂, u₂) to (S A₂ Sᵀ, S(u₂ − u₁)); reason: this is the transformation behind the sentence; with F4 it gives the reduction
--   - generalization: ρ1 thermal, A₁ = coth(β/2) I with β > 0 → A₁ brought to √(det A₁) I; reason: covers the pure case det A₁ = 1 (the vacuum, β = ∞), which a thermal state at finite β cannot express; for det A₁ > 1 it is the thermal state with coth(β/2) = √(det A₁)
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, p.2, paragraph after (13)

import Mathlib
import Definitions.Def_ScutaruFid_L2R
import Definitions.Def_ScutaruFid_IsKernelOperator
import Definitions.Def_ScutaruFid_stateKernel

namespace ScutaruFid

/-- **Reduction to a thermal first state.** Scutaru, arXiv:quant-ph/9708013v1, p.2, paragraph
after (13): "In order to simplify the calculations we shall use the property F4. Then it suffices
to consider that ρ1 is a thermal state (i.e. an undisplaced and unsqueezed state) and that only ρ2
is a displaced squeezed thermal state."

For physical `(A₁, u₁)`, `(A₂, u₂)` (`Aᵢ` symmetric positive definite, `det Aᵢ ≥ 1`) there are a
unitary `U` on `L²(ℝ)` and a real `2 × 2` matrix `S` with `det S = 1` and `S A₁ Sᵀ = √(det A₁) I`
such that, whenever `ρᵢ` has kernel `stateKernel Aᵢ uᵢ`, the operator `Uρ₁U*` has the kernel of
the undisplaced unsqueezed state with matrix `√(det A₁) I`, and `Uρ₂U*` has the kernel of the state
with matrix `S A₂ Sᵀ` and mean `S(u₂ − u₁)`.

**Formalization Note** The page's thermal state is `A₁ = coth(β/2) I`, `β > 0`; `√(det A₁) I`
also covers the pure case `det A₁ = 1` (the vacuum, `β = ∞`). The mean transforms by the same
`S` as the matrix (`A ↦ S A Sᵀ`, `u ↦ S u`, after the translation by `−u₁`), as for the dilation
`ψ(x) ↦ √m ψ(mx)` (`S = diag(1/m, m)`) and the shear `ψ(x) ↦ e^{icx²}ψ(x)`
(`S = [[1, 0], [2c, 1]]`). -/
theorem reduction_to_thermal (A₁ A₂ : Matrix (Fin 2) (Fin 2) ℝ) (u₁ u₂ : Fin 2 → ℝ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hd₁ : 1 ≤ A₁.det) (hd₂ : 1 ≤ A₂.det) :
    ∃ U : L2R →L[ℂ] L2R, U ∈ unitary (L2R →L[ℂ] L2R) ∧
      ∃ S : Matrix (Fin 2) (Fin 2) ℝ, S.det = 1 ∧ S * A₁ * S.transpose = Real.sqrt A₁.det • 1 ∧
        ∀ ρ₁ ρ₂ : L2R →L[ℂ] L2R, IsKernelOperator ρ₁ (stateKernel A₁ u₁) →
          IsKernelOperator ρ₂ (stateKernel A₂ u₂) →
          IsKernelOperator (U * ρ₁ * star U) (stateKernel (Real.sqrt A₁.det • 1) 0) ∧
            IsKernelOperator (U * ρ₂ * star U)
              (stateKernel (S * A₂ * S.transpose) (S.mulVec (u₂ - u₁))) := by sorry

end ScutaruFid
