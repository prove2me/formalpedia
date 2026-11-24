-- Prove2me | Theorems.Thm_ValiantBorder_circuitsToAccelerators
-- name    : ValiantBorder.circuitsToAccelerators
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:33:15.56465+00:00
-- url     : https://prove2.me/theorems/c2cbf66c-9198-4a2c-ac85-3d7927793e68
-- title:
--   From a grid-complete approximating circuit to an accelerator
-- statement:
--   Fix a field, a coefficient subring, finitely supported weights, a scale $H≥32$, and a grid-completeness factor. For suitable constants, an approximating circuit of size $v^a$ for a sufficiently large grid-complete polynomial produces an approximate accelerator at scale $H$ with size $v^{C(a+1)}$, subject to the stated logarithmic restriction on $a$.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/ApproxScales.lean#L487-L545).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/ApproxScales.lean#L487-L545.

import Definitions.Def_ValiantBorder_fieldCases
import Definitions.Def_ValiantBorder_gridComplete
import Definitions.Def_VP_VNP_all_fields
import Definitions.Def_ValiantBorder_approxAccelerator

theorem ValiantBorder.circuitsToAccelerators {K : Type} [Field K] (A : Subring K) (θ : List Bool → A)
    (hθ : (Function.support θ).Finite) {H : ℕ} (hH : 32 ≤ H) (κ : ℕ) :
    ∃ B₀ C v₀ : ℕ, 0 < B₀ ∧ ∀ (G : ∀ S, MvPolynomial (Fin S × Fin S) K),
      ValiantBorder.GridComplete K G κ → ∀ v, v₀ ≤ v → ∀ a, NS1.lg v ^ (C * a) ≤ v → ∀ m, v ^ B₀ ≤ m →
        Statement.Approximates (G m) (v ^ a) → NS1.HasAccA θ K H v (v ^ (C * (a + 1))) := by sorry
