-- Prove2me | Theorems.Thm_SNumbers_sn_eq_singularValues_of_finiteDimensional
-- name    : SNumbers.sn_eq_singularValues_of_finiteDimensional
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:14:29.201157+00:00
-- url     : https://prove2.me/theorems/0cf2e591-bff1-4423-ad3c-89c370dd7944
-- title:
--   SNumbers: sn eq singular Values of finite Dimensional
-- statement:
--   **Singular numbers coincide with all `s`-numbers (finite dimension).** For
--   every `s`-number sequence `s` and operator `S` between finite-dimensional
--   Hilbert spaces, `sₙ(S) = σₙ(S)`.
--
--   Uniqueness reduces `sₙ` to `aₙ` (for *every* `s` at once), and
--   `project_singularValues_eq` identifies `aₙ` with Mathlib's `σₙ`. Specialising
--   `s` to the approximation numbers recovers `aₙ(S) = σₙ(S)`, so no separate
--   statement is needed.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/SingularValuesFinDim.lean#L388-L393
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/SingularValuesFinDim.lean#L388-L393

module
public import Definitions.Def_SNumbers_Uniqueness
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_SingularValuesFinDim
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [FiniteDimensional 𝕜 H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]
variable [Nontrivial H₁] [Nontrivial H₂]
omit [Nontrivial H₁] [Nontrivial H₂]

theorem SNumbers.sn_eq_singularValues_of_finiteDimensional {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : H₁ →L[𝕜] H₂) (n : ℕ) :
    s S n = (S : H₁ →ₗ[𝕜] H₂).singularValues n := by sorry
