-- Prove2me | Theorems.Thm_PHarmNormalize
-- name    : PHarmNormalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:16:07.261955+00:00
-- url     : https://prove2.me/theorems/6f693810-59af-457a-af0e-062e2ad5a0c5
-- title:
--   PHarm Normalize: PHarm Normalize
-- statement:
--   Affine normalization of a `p`-harmonic function.  If `u` is `p`-harmonic on `Ω`
--   with weak gradient `g`, then for every center `x₀`, every dilation factor `r > 0`,
--   every normalizing factor `M > 0` and every additive constant `c`, the function
--   `x ↦ (u (x₀ + r • x) - c) / M` is `p`-harmonic on the rescaled domain
--   `{x | x₀ + r • x ∈ Ω}` with weak gradient `x ↦ (r / M) • g (x₀ + r • x)`.
--
--   This is the rescaling used throughout the paper's iteration: `v ℓ x = v (R • x) / R ^ σ`
--   is the case `x₀ = 0`, `r = R`, `c = 0`, `M = R ^ σ`, and
--   `w x y = (u (x + y / 4) - u x) / M₀` is the case `x₀ = x`, `r = 1 / 4`, `c = u x`,
--   `M = M₀`.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmNormalize.lean#L23-L182
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmNormalize.lean#L23-L182

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
import Definitions.Def_PHigherOrder_AffineTestFunctionPullback
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Definitions.Def_PHigherOrder_NormalizedWeakGradient
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_PHigherOrder_PHarmNormalize
import Theorems.Thm_AffineTestFunctionPullback
import Theorems.Thm_NormalizedWeakGradient
import Theorems.Thm_TestFunctionGradientIntegral
import Theorems.Thm_VanishingOffTsupport

set_option autoImplicit false
set_option linter.unusedVariables false

theorem PHarmNormalize (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (Ω : Set Plane)
    (u : Plane → ℝ) (g : Plane → Plane) (x₀ : Plane) (r M c : ℝ)
    (hr : 0 < r) (hM : 0 < M) (h : IsPHarm p Ω u g) :
    IsPHarm p {x : Plane | x₀ + r • x ∈ Ω}
      (fun x => (u (x₀ + r • x) - c) / M)
      (fun x => (r / M) • g (x₀ + r • x)) := by sorry
