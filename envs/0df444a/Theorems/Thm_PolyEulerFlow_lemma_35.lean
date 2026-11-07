-- Prove2me | Theorems.Thm_PolyEulerFlow_lemma_35
-- name    : PolyEulerFlow.lemma_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:37.549424+00:00
-- url     : https://prove2.me/theorems/346b6bf0-6db8-49ff-b184-aa83af2f2bad
-- title:
--   Lemma 35 — the mesh-uniform cycle, including perturbations
-- statement:
--   With the clock constants of Lemma 31: for every separated affine program and every fixed integer $K\ge256$ there are constants $A,B>0$, $s_0$, a compact box $[lo,hi]$ and a duration constant $C_{cyc}$ such that, for $s\ge s_0$, $h=2^{-s}$, $\varepsilon=h^K$, $0\le\nu\le\varepsilon^2$, every mesh and every disturbance of level $\nu$, the following holds.
--
--   Let a cycle start at a state admissible above a valid configuration $C$ ((36): scalar box, phase-zero entry conditions, $\|Y-C\|_\infty\le r_0h$, $\|Y^s-Y\|_\infty\le A\Delta_\varepsilon$, $v_ju_j(Y,h)>0$, $|v_j|\ge\kappa_0h$), with selected sign pattern $\sigma$. Set $Y_0$ its data and $Y_*=D_\sigma Y_0+b_\sigma$, and assume $\|Y_*-C^+\|_\infty\le r_0h/2$ for the next valid configuration $C^+$. Then the next section (the fourth phase entry) exists, and there
--   $$\|Y-Y_*\|_\infty\le B\Delta_\varepsilon,\tag{37}$$
--   $$\|Y^s-Y\|_\infty\le A\Delta_\varepsilon;\tag{38}$$
--   the conditions on scalars, on the clock and on the comparator cones are restored (the state is admissible above $C^+$); during the whole cycle data and shadows stay within $B\Delta_\varepsilon$ of the segment $[Y_0,Y_*]$ and all active coordinates stay in the box; and the cycle has physical duration at most $C_{cyc}L$.
--
--   This is the local step of the compiler: one clock cycle performs one affine transition with an error $O(\Delta_\varepsilon)$, uniformly in the mesh and the disturbance.
--
--   Differences from the source:
--   - generalization: every mesh 0 < η ≤ 1 (one constant step) → every variable mesh 0 < η_k ≤ 1 with Σ η_k = ∞; reason: Corollary 39 (p.34) states that every clock, cut and cycle estimate holds on such meshes; every constant step in (0, 1] is one of them
--   - reading: the conditions on scalars, on the clock and on the cones of comparators are restored → the state at the next section is admissible above C⁺ in the sense of (36); reason: (36) is the conjunction of these conditions
--   - reading: the entry conditions of the clock for phase zero (in (36)) → (29) with the constants A₀, B₀ of Lemma 31, existential jointly with Lemma 31's other constants; reason: (29) has no other constants
--   - reading: a fixed compact box; physical duration O(L) → a box [lo, hi] and a constant C_cyc chosen with A, B, s₀; duration ≤ C_cyc L; reason: fixed means independent of s, the mesh and the disturbance
--   - encoding: a cycle with index c, starting at t_{4c} → an orbit started at index 0 with the shifted mesh and disturbances; reason: the scheme is autonomous
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Lemma 35, p.32 (PDF 34), with (36) on p.32

import Mathlib
import Definitions.Def_PolyEulerFlow_IsCycleConstants

namespace PolyEulerFlow

/-- **Lemma 35 (Mesh-uniform cycle, including perturbations)**, p.32 (PDF 34). Bournez, One Polynomial Field for Every Euler Step and the
Flow (manuscript, sha256 c4e01b2b…).

With the clock constants of Lemma 31: for every separated affine program and every fixed integer `K ≥ 256` there are constants `A, B, s₀ > 0`
(and a compact box and a duration constant) such that, for `s ≥ s₀`, `ε = h^K`, `0 ≤ ν ≤ ε²` and every mesh: if a cycle starts at a state
admissible above a valid `C` with source sign pattern `σ`, `Y₀` its data, `Y∗ = D_σY₀ + b_σ`, and `‖Y∗ - C⁺‖∞ ≤ r₀h/2` for the next valid
configuration `C⁺`, then at the next section (37) `‖Y - Y∗‖∞ ≤ B∆ε` and (38) `‖Y^s - Y‖∞ ≤ A∆ε`, the scalar, clock and comparator-cone conditions
are restored (the state is admissible above `C⁺`), during the whole cycle data and shadows stay within `B∆ε` of the segment `[Y₀, Y∗]` and all active
coordinates stay in the fixed box, and the cycle lasts `O(L)` physical time. See `IsCycleConstants`.

**Formalization Note** The mesh is variable (Corollary 39, p.34), containing every constant `η ∈ (0, 1]`. Admissibility (36) refers to the entry
conditions (29), whose constants `A₀, B₀` are those of Lemma 31; they are therefore existential together with the rest of Lemma 31. -/
theorem lemma_35 :
    ∃ A0 B0 Cdur Cenv Cnext Dclk ε0 : ℝ, IsUniformClock A0 B0 Cdur Cenv Cnext Dclk ε0 ∧
    ∀ (m g : ℕ) (prog : SeparatedAffineProgram m g) (K : ℕ), 256 ≤ K →
      ∃ (A B : ℝ) (s0 : ℕ) (lo hi : CompiledState m g) (Ccyc : ℝ), 0 < s0 ∧
        IsCycleConstants prog K A0 B0 A B s0 lo hi Ccyc := by sorry

end PolyEulerFlow
