-- Prove2me | Theorems.Thm_PHarmWeakGradClassical
-- name    : PHarmWeakGradClassical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:11:16.005797+00:00
-- url     : https://prove2.me/theorems/d9d5911d-0785-4d7b-bf36-4f7fe4a42042
-- title:
--   PHarm Weak Grad Classical: PHarm Weak Grad Classical
-- statement:
--   The weak-to-classical gradient bridge.  If `u` is `p`-harmonic on `Ω` with some
--   weak gradient `g`, and `u` happens to be `C^1` on `Ω`, then `u` is `p`-harmonic on
--   `Ω` with its own CLASSICAL gradient as weak gradient, and `g = gradient u` almost
--   everywhere on `Ω`.
--
--   This is what lets a statement whose hypothesis is the paper's -- `p`-harmonic with a
--   general `L^p_loc` weak gradient -- be fed to machinery that produces or consumes the
--   classical gradient.  The two equalities are not interchangeable: a weak gradient is
--   determined only up to a null set, so no pointwise congruence can replace this.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmWeakGradClassical.lean#L14-L192
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmWeakGradClassical.lean#L14-L192

import Definitions.Def_PHigherOrder_IsPHarm
import Definitions.Def_PHigherOrder_TestFunctionGradientIntegral
import Definitions.Def_PHigherOrder_VanishingOffTsupport
import Definitions.Def_PHigherOrder_PHarmWeakGradClassical
import Theorems.Thm_TestFunctionGradientIntegral
import Theorems.Thm_VanishingOffTsupport

set_option autoImplicit false

theorem PHarmWeakGradClassical (p : ℝ) (hp : 1 < p) (Ω : Set Plane)
    (u : Plane → ℝ) (g : Plane → Plane)
    (h : IsPHarm p Ω u g) (hu : ContDiffOn ℝ 1 u Ω) :
    IsPHarm p Ω u (gradient u) ∧ ∀ᵐ x, x ∈ Ω → g x = gradient u x := by sorry
