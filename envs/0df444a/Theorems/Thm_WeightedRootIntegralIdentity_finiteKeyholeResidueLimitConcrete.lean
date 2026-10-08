-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_finiteKeyholeResidueLimitConcrete
-- name    : WeightedRootIntegralIdentity.finiteKeyholeResidueLimitConcrete
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T11:33:43.30653+00:00
-- url     : https://prove2.me/theorems/0ae41d5a-bb3a-4286-b080-fbb41db46cb6
-- statement:
--   Let the six finite keyhole contour components be upper bank, lower bank, right and left vertical sides, inner arc, and outer arc. Assume the finite contour identity is the residue theorem identity, the four auxiliary components vanish along the canonical sequence, and the two banks converge to boundary values A and B. Then the limiting bank sum equals the residue contribution. If the boundary phases on the interval between successive branch points are recorded by sin(π∑_{i≤k}w_i), the bank sum is the corresponding weighted real-axis jump.

import Mathlib
open scoped BigOperators
open Filter Topology

theorem WeightedRootIntegralIdentity.finiteKeyholeResidueLimitConcrete
    (n : ℕ) (w : ℕ → ℝ) (J : ℕ → ℂ)
    (U L VR VL I O : ℕ → ℂ) (res A B : ℂ)
    (hfinite : ∀ m : ℕ,
      U m + L m + VR m + VL m + I m + O m =
        2 * (Real.pi : ℂ) * Complex.I * res)
    (hVR : Tendsto VR atTop (𝓝 0))
    (hVL : Tendsto VL atTop (𝓝 0))
    (hI : Tendsto I atTop (𝓝 0))
    (hO : Tendsto O atTop (𝓝 0))
    (hU : Tendsto U atTop (𝓝 A))
    (hL : Tendsto L atTop (𝓝 B))
    (hphase : A + B =
      ∑ k ∈ Finset.range (n - 1),
        (2 * Complex.I * (Real.sin
          (Real.pi * ∑ i ∈ Finset.range (k + 1), w i) : ℂ)) * J k) :
    A + B = 2 * (Real.pi : ℂ) * Complex.I * res ∧
      A + B =
        ∑ k ∈ Finset.range (n - 1),
          (2 * Complex.I * (Real.sin
            (Real.pi * ∑ i ∈ Finset.range (k + 1), w i) : ℂ)) * J k := by sorry
