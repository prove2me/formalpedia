-- Prove2me | Theorems.Thm_SumProduct_dedekindZeta_completed_residue_le
-- name    : SumProduct.dedekindZeta_completed_residue_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:02:40.291797+00:00
-- url     : https://prove2.me/theorems/9ddda2af-bf84-4d1c-be96-3044d6d1257b
-- title:
--   Sum Product: dedekind Zeta completed residue le
-- statement:
--   **Functional-equation residue bound** for totally real `K`: the **specialization** of Hecke's
--   functional equation `dedekindZeta_completed_ge_residue` to the totally real case (`nrComplexPlaces
--   K = 0`, so the complex Γ-factor drops out and `nrRealPlaces K = d`), divided by `√|Δ_K|`.  For
--   `s > 1`, `κ_K ≤ s(s-1)|Δ_K|^{(s-1)/2}π^{-ds/2}Γ(s/2)^d ζ_K(s)`.
--
--   For totally real `K` the residue is `ρ = κ_K√|Δ_K|` (the `1/π^{r₂}` is `1`), so
--   `dedekindZeta_completed_ge_residue` reads
--   `κ_K√|Δ_K| ≤ s(s-1)|Δ_K|^{s/2}(π^{-s/2}Γ(s/2))^d ζ_K(s)`; since
--   `(π^{-s/2}Γ(s/2))^d = π^{-ds/2}Γ(s/2)^d` and `|Δ_K|^{s/2} = |Δ_K|^{(s-1)/2}√|Δ_K|`, dividing by
--   `√|Δ_K| > 0` gives the claim.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/RegulatorBound.lean#L118-L161
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/RegulatorBound.lean#L118-L161

import Definitions.Def_SumProduct_PartialZetaMellin
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_EulerBound
import Definitions.Def_SumProduct_RegulatorBound
set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.InfinitePlace

theorem SumProduct.dedekindZeta_completed_residue_le (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (s : ℝ) (hs : 1 < s) :
    NumberField.dedekindZeta_residue K ≤
      s * (s - 1) * |(NumberField.discr K : ℝ)| ^ ((s - 1) / 2)
        * Real.pi ^ (-(Module.finrank ℚ K : ℝ) * s / 2)
        * Real.Gamma (s / 2) ^ Module.finrank ℚ K
        * (NumberField.dedekindZeta K (s : ℂ)).re := by sorry
