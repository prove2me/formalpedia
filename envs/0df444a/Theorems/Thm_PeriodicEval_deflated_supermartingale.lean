-- Prove2me | Theorems.Thm_PeriodicEval_deflated_supermartingale
-- name    : PeriodicEval.deflated_supermartingale
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:09:15.014589+00:00
-- url     : https://prove2.me/theorems/630cb0f2-ecce-47fb-8b9d-86a0fa36db6d
-- title:
--   Proof of Theorem 1, p.43 — deflated wealth $ZX$ is a supermartingale
-- statement:
--   Under the standing assumptions, for every $x>0$ and every $X\in\mathcal A_0(x)$, the deflated wealth $(Z_tX_t)_{t\ge0}$ is a supermartingale with respect to $(\mathcal F_t)$; in particular
--
--   $$E[Z_{T_{n+1}}X_{T_{n+1}}\mid\mathcal F_{T_n}]\le Z_{T_n}X_{T_n}.$$
--
--   This is the budget constraint of a nonnegative self-financing portfolio between evaluation dates.
--
--   Differences from the source: none.
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), proof of Theorem 1, p.43

import Mathlib
import Definitions.Def_PeriodicEval_Objective
import Definitions.Def_PeriodicEval_Auxiliary

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicEval

/-- Deflated wealth is a supermartingale, SSRN 3971852 (June 20, 2023), proof of Theorem 1,
p.43: "Since `X ∈ A_0(x)`, `ZX` is a supermartingale and hence
`E[Z_{T_{n+1}}X_{T_{n+1}} | ℱ_{T_n}] ≤ Z_{T_n}X_{T_n}`." -/
theorem deflated_supermartingale (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) (x : ℝ) (hx : 0 < x) (X : ℝ≥0 → Ω → ℝ)
    (hX : X ∈ admissible p P ℱ B 0 x) :
    Supermartingale (fun t ω => Z p B t ω * X t ω) ℱ P := by sorry

end PeriodicEval
