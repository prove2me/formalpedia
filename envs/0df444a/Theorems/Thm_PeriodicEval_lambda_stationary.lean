-- Prove2me | Theorems.Thm_PeriodicEval_lambda_stationary
-- name    : PeriodicEval.lambda_stationary
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:55.286996+00:00
-- url     : https://prove2.me/theorems/90013ec5-5b90-43aa-876b-cc2504747220
-- title:
--   Proof of Theorem 1, pp.43–44 — the multiplier is the same in every period
-- statement:
--   Under the standing assumptions, let $y\ge0$ be measurable and $\lambda>0$ with $Z_\tau y(\lambda Z_\tau)$ integrable. For every $n$, the period-$n$ variable $\frac{Z_{T_{n+1}}}{Z_{T_n}}y\big(\lambda\frac{Z_{T_{n+1}}}{Z_{T_n}}\big)$ is integrable and
--
--   $$E\Big[\frac{Z_{T_{n+1}}}{Z_{T_n}}\,y\Big(\lambda\frac{Z_{T_{n+1}}}{Z_{T_n}}\Big)\ \Big|\ \mathcal F_{T_n}\Big]=E[Z_\tau\,y(\lambda Z_\tau)]\quad\text{a.s.}$$
--
--   This is the stationary-increment property of the pricing kernel; it gives $\lambda^*_n=\lambda^*$ for all $n$ in the proof of Theorem 1.
--
--   Differences from the source:
--   - generalization: y = y*_{A*} and λ = λ*_n → every measurable y ≥ 0 and λ > 0 with Z_τ y(λZ_τ) integrable; reason: the paper's instance satisfies the hypotheses (E[Z_τ y*_{A*}(λ*Z_τ)] = 1); the integrability makes the conditional expectation genuine
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), proof of Theorem 1, pp.43–44

import Mathlib
import Definitions.Def_PeriodicEval_Objective
import Definitions.Def_PeriodicEval_Auxiliary

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicEval

/-- Stationarity of the multiplier, SSRN 3971852 (June 20, 2023), proof of Theorem 1, pp.43–44:
"since `Z` has the form given by (1), the stationary increment property of Brownian motion
implies that `E[(Z_{T_{n+1}}/Z_{T_n}) y*_{A*}(λ*_n Z_{T_{n+1}}/Z_{T_n}) | ℱ_{T_n}] =
E[(Z_{T_1}/Z_{T_0}) y*_{A*}(λ*_n Z_{T_1}/Z_{T_0}) | ℱ_{T_0}] = E[Z_τ y*_{A*}(λ*Z_τ)]` for all `n`".

Stated for every measurable `y ≥ 0` and every `λ > 0` with `Z_τ y(λZ_τ)` integrable: the
period-`n` variable is integrable and its conditional expectation given `ℱ_{T_n}` is the
constant `E[Z_τ y(λZ_τ)]`.

**Formalization Note** The paper's `y*_{A*}` and `λ*_n` are instances; integrability of
`Z_τ y(λZ_τ)` is assumed so that the conditional expectation is genuine (in the paper the
value is `1`). -/
theorem lambda_stationary (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) (y : ℝ → ℝ) (hy : Measurable y) (hy0 : ∀ q, 0 ≤ y q)
    (lam : ℝ) (hlam : 0 < lam)
    (hint : Integrable (fun ω => Z p B p.τ.toNNReal ω * y (lam * Z p B p.τ.toNNReal ω)) P)
    (n : ℕ) :
    Integrable (fun ω => Z p B (p.T (n + 1)) ω / Z p B (p.T n) ω *
      y (lam * (Z p B (p.T (n + 1)) ω / Z p B (p.T n) ω))) P ∧
    P[fun ω => Z p B (p.T (n + 1)) ω / Z p B (p.T n) ω *
        y (lam * (Z p B (p.T (n + 1)) ω / Z p B (p.T n) ω)) | ℱ (p.T n)] =ᵐ[P]
      fun _ => ∫ ω, Z p B p.τ.toNNReal ω * y (lam * Z p B p.τ.toNNReal ω) ∂P := by sorry

end PeriodicEval
