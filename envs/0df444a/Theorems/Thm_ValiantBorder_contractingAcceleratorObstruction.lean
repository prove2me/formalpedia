-- Prove2me | Theorems.Thm_ValiantBorder_contractingAcceleratorObstruction
-- name    : ValiantBorder.contractingAcceleratorObstruction
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:33:23.948853+00:00
-- url     : https://prove2.me/theorems/2c92e14c-41c4-41e1-bf8e-82e29c9f2c93
-- title:
--   Contracting fields obstruct approximate accelerators
-- statement:
--   For a contracting field there is a coefficient subring with finitely supported weights and an integer scale $h≥17$ for which sufficiently large instances admit no approximate accelerator of size $v^a$ whenever $(1+\lfloor\log_2 v\rfloor)^{Ca}≤v$ for a suitable constant $C$.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/ApproxScales.lean#L469).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/ApproxScales.lean#L469.

import Definitions.Def_ValiantBorder_fieldCases
import Definitions.Def_ValiantBorder_gridComplete
import Definitions.Def_VP_VNP_all_fields
import Definitions.Def_ValiantBorder_approxAccelerator

theorem ValiantBorder.contractingAcceleratorObstruction {K : Type} [Field K] (hK : Paper.Contracting K) :
    ∃ (A : Subring K) (θ : List Bool → A) (h : ℕ), (Function.support θ).Finite ∧ 17 ≤ h ∧
      ∃ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∀ a, NS1.lg v ^ (C * a) ≤ v →
        ¬ NS1.HasAccA θ K (16 * h) v (v ^ a) := by sorry
