-- Prove2me | Theorems.Thm_WeierstrassCurve_discr_dvd_pow_of_jOfUnit_mem_range_short
-- name    : WeierstrassCurve.discr_dvd_pow_of_jOfUnit_mem_range_short
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/a54adb2f-cec0-5eae-b7df-2a28e18efa79
-- title:
--   Integral j forces Δ ∣ a³ and Δ ∣ b²
-- statement:
--   Let $R_0$ be an integral domain and $K$ a field which is a fraction field of $R_0$ (via the given algebra structure), both in the same universe. Assume that the images of $2$ and of $3$ in $R_0$ are units, and let $a, b \in R_0$. Write $W_0$ for the Weierstrass curve $\langle a_1,a_2,a_3,a_4,a_6\rangle = \langle 0,0,0,a,b\rangle$ over $R_0$, that is $y^2 = x^3 + ax + b$. Assume that the discriminant $\Delta$ of the base change of $W_0$ along $R_0 \to K$ is a unit of $K$ (equivalently, nonzero), and that the $j$-invariant of that base-changed curve — formed as `jOfUnit`, which by definition is the $j$-invariant of the curve regarded as elliptic by virtue of the invertibility of $\Delta$ — lies in the image of $R_0 \to K$. The conclusion is a pair of divisibilities in $R_0$: the discriminant $\Delta(W_0)$ divides $a^3$, and $\Delta(W_0)$ divides $b^2$.
--
--   This is the elementary divisibility content of the implication "integral $j$-invariant $\Rightarrow$ potentially good reduction" for a short Weierstrass model over a base in which $6$ is invertible; over a discrete valuation ring it reads $3v(a) \ge v(\Delta)$ and $2v(b) \ge v(\Delta)$. It is used in the construction of an explicit variable change bringing a curve with level-$p$ structure and integral $j$-invariant into a prescribed integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_discr_dvd_pow_of_jOfUnit_mem_range_short.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.discr_dvd_pow_of_jOfUnit_mem_range_short
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (h2 : IsUnit ((2 : ℕ) : R₀)) (h3 : IsUnit ((3 : ℕ) : R₀)) (a b : R₀)
    (hΔ : IsUnit ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K)).Δ)
    (hj : ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K)).jOfUnit hΔ ∈ Set.range (algebraMap R₀ K)) :
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).Δ ∣ a ^ 3 ∧ (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).Δ ∣ b ^ 2 := by sorry
