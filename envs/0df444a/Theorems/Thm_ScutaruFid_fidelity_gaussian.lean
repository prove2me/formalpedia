-- Prove2me | Theorems.Thm_ScutaruFid_fidelity_gaussian
-- name    : ScutaruFid.fidelity_gaussian
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:58.35825+00:00
-- url     : https://prove2.me/theorems/36a3a829-e86d-4c4a-a78c-b72b2dd6b33c
-- title:
--   Eq. (17): $F(\rho_1,\rho_2)=\frac{2}{\sqrt{\Delta+T}-\sqrt T}\exp[-u^{\mathsf T}(A_1+A_2)^{-1}u]$ for any two single-mode Gaussian states
-- statement:
--   Let $A_1,A_2$ be real symmetric positive definite $2\times2$ matrices with $\det A_1\ge1$, $\det A_2\ge1$, let $u_1,u_2\in\mathbb R^2$, and let $\rho_j$ be the operator on $L^2(\mathbb R)$ with kernel `stateKernel A_j u_j`: the Gaussian (displaced squeezed thermal) state whose matrix (11) is $A_j$ (twice the covariance matrix of $(Q,P)$, so that the vacuum has $A=I$) and whose vector of means $(\langle Q\rangle,\langle P\rangle)$ is $u_j$. Then Uhlmann's fidelity is
--
--   $$
--   F(\rho_1,\rho_2)=\frac{2}{\sqrt{\Delta+T}-\sqrt T}\,\exp\big[-u^{\mathsf T}(A_1+A_2)^{-1}u\big],
--   $$
--
--   where
--
--   $$
--   \Delta=\det(A_1+A_2),\qquad T=(\det A_1-1)(\det A_2-1),\qquad u=u_2-u_1 ,
--   $$
--
--   and the trace in $F$ may be computed in any Hilbert basis of $L^2(\mathbb R)$. Pure states ($\det A_j=1$, $T=0$) are included.
--
--   This closed form covers every pair of single-mode Gaussian states, displaced and squeezed; for $u=0$ it gives Twamley's result for undisplaced thermal states, and for $A_1=A_2=I$ it gives $|\langle\beta_1|\beta_2\rangle|^2=e^{-|u|^2/2}$ for coherent states.
--
--   Differences from the source:
--   - reading: u = (α, τ), the displacement of ρ2 with ρ1 thermal at the origin → u = u₂ − u₁, the difference of the mean vectors; reason: in the general-validity remark (pp.2–3) this is the only reading under which the claim follows from F4: a common displacement is unitary, and (A, u) ↦ (S A Sᵀ, S u) with det S = 1 leaves the formula unchanged
--   - generalization: (17) derived for ρ1 thermal and ρ2 displaced squeezed thermal → any two displaced squeezed thermal states; reason: the paper claims this itself (pp.2–3, via F4); the derived case is u₁ = 0, A₁ = coth(β/2) I
--   - encoding: displaced squeezed thermal states with matrices A_i and displacement u → operators with kernel stateKernel A_i u_i, A_i symmetric positive definite with det A_i ≥ 1; reason: the paper's model (p.1: Gaussian density operators are integral operators with kernel (3)); the matrix conditions are "Re a ≥ −b ≥ 0" (p.1) through (12)–(13) and exclude only non-states
--   - encoding: trace in F → operatorTrace in an arbitrary Hilbert basis; F = (Re trace √(√ρ1 ρ2 √ρ1))²; reason: the trace of the trace-class positive operator √(√ρ1 ρ2 √ρ1) is real and basis-independent
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eq. (17), p.2, and the general-validity remark pp.2–3 ("due to F4 the formula (17) is generaly valid i.e. for any two displaced squeezed thermal states")

import Mathlib
import Definitions.Def_ScutaruFid_L2R
import Definitions.Def_ScutaruFid_IsKernelOperator
import Definitions.Def_ScutaruFid_stateKernel
import Definitions.Def_ScutaruFid_fidelity

open Matrix

namespace ScutaruFid

/-- **Fidelity of two single-mode Gaussian states**, eq. (17). Scutaru, arXiv:quant-ph/9708013v1,
eq. (17), p.2: "After long but simple calculations we obtain the main result of the paper:
F(ρ1, ρ2) = 2/(√(∆ + T) − √T) exp[−uᵀ(A1 + A2)⁻¹u] (17) where ∆ = det(A1 + A2),
T = (detA1 − 1)(detA2 − 1) and where u is the column vector (α, τ)", with pp.2–3: "We remark that
due to F4 the formula (17) is generaly valid i.e. for any two displaced squeezed thermal states."

Let `A₁, A₂` be real symmetric positive definite `2 × 2` matrices with `det Aᵢ ≥ 1` and
`u₁, u₂ ∈ ℝ²`, and let `ρᵢ` be the operator on `L²(ℝ)` with kernel `stateKernel Aᵢ uᵢ` (the
Gaussian state with matrix `Aᵢ`, twice its covariance matrix, and mean vector `uᵢ`). Then for every
Hilbert basis used for the trace,
`F(ρ₁, ρ₂) = 2/(√(Δ + T) − √T) · exp[−vᵀ(A₁ + A₂)⁻¹v]`,
`Δ = det(A₁ + A₂)`, `T = (det A₁ − 1)(det A₂ − 1)`, `v = u₂ − u₁`.

**Formalization Note** The paper derives (17) for `ρ₁` thermal at the origin, where its `u` is
the displacement of `ρ₂`; for two arbitrary states `u` is the difference `u₂ − u₁` of the mean
vectors. Pure states (`det Aᵢ = 1`, `T = 0`) are included. -/
theorem fidelity_gaussian (A₁ A₂ : Matrix (Fin 2) (Fin 2) ℝ) (u₁ u₂ : Fin 2 → ℝ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hd₁ : 1 ≤ A₁.det) (hd₂ : 1 ≤ A₂.det)
    (ρ₁ ρ₂ : L2R →L[ℂ] L2R) (h₁ : IsKernelOperator ρ₁ (stateKernel A₁ u₁))
    (h₂ : IsKernelOperator ρ₂ (stateKernel A₂ u₂)) {ι : Type*} (B : HilbertBasis ι ℂ L2R) :
    let Δ := (A₁ + A₂).det
    let T := (A₁.det - 1) * (A₂.det - 1)
    let v := u₂ - u₁
    fidelity B ρ₁ ρ₂ =
      2 / (Real.sqrt (Δ + T) - Real.sqrt T) * Real.exp (-(v ⬝ᵥ ((A₁ + A₂)⁻¹ *ᵥ v))) := by sorry

end ScutaruFid
