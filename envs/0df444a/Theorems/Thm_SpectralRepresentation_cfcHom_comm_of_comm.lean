-- Prove2me | Theorems.Thm_SpectralRepresentation_cfcHom_comm_of_comm
-- name    : SpectralRepresentation.cfcHom_comm_of_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:15:57.91105+00:00
-- url     : https://prove2.me/theorems/3ecd2bf8-29f6-5a57-9c4a-8eace68aef58
-- title:
--   Spectral Representation: cfc Hom comm of comm
-- statement:
--   **Commutation with the functional calculus.** A continuous `ℝ`-linear map `J` of `H₁`
--   that commutes with a self-adjoint `P` commutes with `cfcHom hP f` for *every* continuous
--   symbol `f`. Proved by the Stone–Weierstrass induction on `f` (constants, `id`, sums, products,
--   and a closure step), exactly as Mathlib's `Commute.cfcHom`, but here `J` is an *external* map
--   (it may even be conjugate-linear over `ℂ`, only `ℝ`-linearity is used), which is why we cannot
--   use the algebra-internal version.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L110-L138
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L110-L138

module
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Definitions.Def_BasicResults_Spectral_Projection
set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap
open SpectralRepresentation
open Filter Topology
open scoped InnerProductSpace
variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

theorem SpectralRepresentation.cfcHom_comm_of_comm {P : H₁ →L[ℂ] H₁} (hP : IsSelfAdjoint P)
    (J : H₁ →L[ℝ] H₁) (hJP : ∀ x, J (P x) = P (J x)) (f : C(spectrum ℝ P, ℝ)) :
    ∀ x, J (cfcHom hP f x) = cfcHom hP f (J x) := by sorry
