-- Prove2me | Theorems.Thm_SNumbers_prod_approximationNumber_eq_norm_det
-- name    : SNumbers.prod_approximationNumber_eq_norm_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:28:27.794445+00:00
-- url     : https://prove2.me/theorems/2dd7b583-cd75-4bf8-a229-6e3fca1cc8a8
-- title:
--   SNumbers: prod approximation Number eq norm det
-- statement:
--   **`∏ aₖ(T) = ‖det T‖`** for an endomorphism of a finite-dimensional Hilbert
--   space. The approximation numbers are Mathlib's singular values
--   (`sn_eq_singularValues_of_finiteDimensional`), and `‖det T‖ = ∏ σₖ` is Mathlib's
--   `LinearMap.normDet_eq_prod_singularValues` read through
--   `LinearMap.normDet_eq_norm_det`. This is the determinant ingredient of the
--   maximal difference theorem.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L628-L634
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L628-L634

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]

theorem SNumbers.prod_approximationNumber_eq_norm_det {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [Nontrivial E] (T : E →L[𝕜] E) :
    ∏ k ∈ Finset.range (Module.finrank 𝕜 E), approximationNumber T k
      = ‖LinearMap.det (T : E →ₗ[𝕜] E)‖ := by sorry
