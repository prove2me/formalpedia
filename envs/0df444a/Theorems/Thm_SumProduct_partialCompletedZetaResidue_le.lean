-- Prove2me | Theorems.Thm_SumProduct_partialCompletedZetaResidue_le
-- name    : SumProduct.partialCompletedZetaResidue_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:02:28.557064+00:00
-- url     : https://prove2.me/theorems/b75ac4d8-f678-4a1f-9228-09b669493f5c
-- title:
--   Sum Product: partial Completed Zeta Residue le
-- statement:
--   **Per-ideal residue inequality, proved directly from the local decomposition.** For real
--   `s > 1`, dedekind's completed partial zeta dominates its pole residue after multiplying by
--   `s*(s-1)`: `partialCompletedZetaResidue K ≤ s*(s-1)*(completedPartialZeta K 𝔞 (s:ℂ)).re`.
--
--   This is the exact analytic fact used downstream. Compared with the former bridge through the full
--   existential `partialCompletedZeta_mellin_formula`, this proof stops at the `u`-tail form supplied by
--   the reflection identity and drops the explicit `Φ, Ψ` density packaging.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L995-L1233
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/PartialZetaMellin.lean#L995-L1233

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open SumProduct
variable (K : Type*) [Field K] [NumberField K]
open DedekindZeta DedekindZeta.ConeRadialReduction DedekindZeta.ConeMellinBridge
  DedekindZeta.MellinPrinciple
open scoped nonZeroDivisors
variable {K}

theorem SumProduct.partialCompletedZetaResidue_le (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) {s : ℝ} (hs : 1 < s) :
    partialCompletedZetaResidue K ≤
      s * (s - 1) * (DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ)).re := by sorry
