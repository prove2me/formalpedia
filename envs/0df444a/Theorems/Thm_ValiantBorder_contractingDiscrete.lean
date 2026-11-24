-- Prove2me | Theorems.Thm_ValiantBorder_contractingDiscrete
-- name    : ValiantBorder.contractingDiscrete
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:26:57.734403+00:00
-- url     : https://prove2.me/theorems/1f29869f-1921-4f0e-8848-5ae6cef4a6f4
-- title:
--   A discrete circuit lower bound in the contracting case
-- statement:
--   For each grid-complete family over a contracting field, there are constants $C$ and $M_1$ such that, for $M≥M_1$, a circuit of size $M^a$ cannot approximate the size-$M$ polynomial whenever $(\lfloor\log_2 M\rfloor+1)^{Ca}≤M$.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/ApproxScales.lean#L507).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/ApproxScales.lean#L507.

import Definitions.Def_ValiantBorder_fieldCases
import Definitions.Def_ValiantBorder_gridComplete
import Definitions.Def_VP_VNP_all_fields

theorem ValiantBorder.contractingDiscrete {K : Type} [Field K] (hK : Paper.Contracting K)
    {G : ∀ S, MvPolynomial (Fin S × Fin S) K} {κ : ℕ} (hG : ValiantBorder.GridComplete K G κ) :
    ∃ C M₁ : ℕ, ∀ M ≥ M₁, ∀ a : ℕ, (Nat.log 2 M + 1) ^ (C * a) ≤ M →
      ¬ Statement.Approximates (G M) (M ^ a) := by sorry
