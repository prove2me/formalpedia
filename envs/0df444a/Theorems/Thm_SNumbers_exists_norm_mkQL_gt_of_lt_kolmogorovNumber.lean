-- Prove2me | Theorems.Thm_SNumbers_exists_norm_mkQL_gt_of_lt_kolmogorovNumber
-- name    : SNumbers.exists_norm_mkQL_gt_of_lt_kolmogorovNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:58:14.555865+00:00
-- url     : https://prove2.me/theorems/cd06474c-d4d6-4269-b123-3993cf3b605d
-- title:
--   SNumbers: exists norm mk QL gt of lt kolmogorov Number
-- statement:
--   **Iterative point selection for the Kolmogorov numbers (dual).** If `c < dₖ(S)` and `V` is a
--   subspace of `Y` of dimension `≤ k`, there is `x` with `‖x‖ ≤ 1` and `‖π_V(S x)‖ > c`
--   (since `dₖ(S) ≤ ‖π_V ∘ S‖`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L693-L698
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L693-L698

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
omit [CompleteSpace X] [CompleteSpace Y]

theorem SNumbers.exists_norm_mkQL_gt_of_lt_kolmogorovNumber (S : X →L[𝕜] Y) {k : ℕ} {V : Submodule 𝕜 Y}
    (hV_rank : Module.rank 𝕜 V ≤ (k : Cardinal)) {c : ℝ} (hc : c < kolmogorovNumber S k) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ c < ‖V.mkQL (S x)‖ := by sorry
