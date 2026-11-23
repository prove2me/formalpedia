-- Prove2me | Theorems.Thm_P2M_DedekindZeta_Theta_inner_eEmb__991a1bff15f2
-- name    : P2M_DedekindZeta_Theta_inner_eEmb__991a1bff15f2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:10:47.555785+00:00
-- url     : https://prove2.me/theorems/30b2c7ce-d015-47e3-9a96-d0ad95b68893
-- title:
--   P2 M Dedekind Zeta Theta inner e Emb  991a1bff15f2: P2 M Dedekind Zeta Theta inner e Emb  991a1bff15f2
-- statement:
--   **ℝ-bilinear extension of `inner_eEmb`.** For an arbitrary point
--   `ξ : mixedSpace K = K_ℝ` and `y : K`, the Minkowski inner product of `eEmbℝ ξ`
--   (the `ℝ`-linear extension of `eEmb`) against `eEmb y` is the place-sum Hermitian
--   pairing `B(ξ, y)` (the standard treatment): the factor `2` on the complex places
--   comes from the `√2`-weighting baked into `eEmbℝ`/`eEmb`. Specialising
--   `ξ = mixedEmbedding K x` recovers `inner_eEmb`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L276-L308
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L276-L308

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem P2M_DedekindZeta_Theta_inner_eEmb__991a1bff15f2 (ξ : mixedSpace K) (y : K) :
    (inner ℝ (eEmbℝ K ξ) (eEmb K y) : ℝ) =
      (∑ w : {w : InfinitePlace K // w.IsReal},
          ξ.1 w * (mixedEmbedding K y).1 w) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
          (starRingEnd ℂ (ξ.2 w) * (mixedEmbedding K y).2 w).re := by sorry

alias «DedekindZeta».«Theta».«inner_eEmbℝ» := P2M_DedekindZeta_Theta_inner_eEmb__991a1bff15f2
