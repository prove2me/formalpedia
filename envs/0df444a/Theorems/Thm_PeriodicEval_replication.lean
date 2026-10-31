-- Prove2me | Theorems.Thm_PeriodicEval_replication
-- name    : PeriodicEval.replication
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:09:08.93029+00:00
-- url     : https://prove2.me/theorems/131c2b06-fba8-46db-b334-0f6338ebb63d
-- title:
--   Proof of Theorem 1, p.44 — replication of a budget-feasible sequence $H_n$
-- statement:
--   Under the standing assumptions, let $x>0$ and let $(H_n)_{n\ge0}$ be random variables with $H_0=x$, $H_n\ge0$ $\mathcal F_{T_n}$-measurable, and
--
--   $$E[Z_{T_{n+1}}H_{n+1}\mid\mathcal F_{T_n}]\le Z_{T_n}H_n\quad\text{for all }n.$$
--
--   Then there is $\hat X\in\mathcal A_0(x)$ with $\hat X_{T_n}=H_n$ almost surely for all $n$. This uses the martingale representation theorem in the Brownian filtration and, when the budget is not binding, a "doubling down" strategy that burns the surplus (Duffie (2001), pp.103–104).
--
--   Differences from the source:
--   - generalization: H_n = H_{n−1} y*_{A*}(λ*Z_{T_n}/Z_{T_{n−1}}), H_0 = x → every nonnegative adapted (H_n) with H_0 = x and the conditional budget inequality; reason: the paper's argument uses only these properties, which its H_n has
--   - encoding: E[Z_{T_{n+1}}H_{n+1} | F_{T_n}] ≤ Z_{T_n}H_n → Z_{T_{n+1}}H_{n+1} integrable and the inequality for the conditional expectation; reason: for nonnegative H the inequality forces integrability by induction from H_0 = x
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), proof of Theorem 1, p.44

import Mathlib
import Definitions.Def_PeriodicEval_Objective
import Definitions.Def_PeriodicEval_Auxiliary

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PeriodicEval

/-- Replication, SSRN 3971852 (June 20, 2023), proof of Theorem 1, p.44: for `H_n ∈ F⁺_{T_n}`
with `H_0 = x` and `E[Z_{T_{n+1}}H_{n+1} | ℱ_{T_n}] ≤ Z_{T_n}H_n`, "using standard arguments of
martingale representation theorem, there exists `X̂ ∈ A_0(x)` such that `X̂_{T_n} = H_n` for
all `n`" (including the strict-supermartingale case, replicated by a "doubling down" style
strategy, Duffie (2001) pp.103–104).

Stated for every such sequence `(H_n)`, of which the paper's `H_n = H_{n−1}y*_{A*}(λ*Z_{T_n}/Z_{T_{n−1}})`
is an instance.

**Formalization Note** `H_n` is nonnegative and `ℱ_{T_n}`-measurable; `Z_{T_{n+1}}H_{n+1}` is
required integrable so that the conditional expectation is genuine (for nonnegative `H` this
follows from the inequality by induction). Equalities `X̂_{T_n} = H_n` hold almost surely. -/
theorem replication (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) (x : ℝ) (hx : 0 < x) (H : ℕ → Ω → ℝ) (hH0 : ∀ ω, H 0 ω = x)
    (hHmeas : ∀ n, Measurable[ℱ (p.T n)] (H n)) (hHnn : ∀ n ω, 0 ≤ H n ω)
    (hHint : ∀ n, Integrable (fun ω => Z p B (p.T (n + 1)) ω * H (n + 1) ω) P)
    (hHsup : ∀ n, P[fun ω => Z p B (p.T (n + 1)) ω * H (n + 1) ω | ℱ (p.T n)] ≤ᵐ[P]
      fun ω => Z p B (p.T n) ω * H n ω) :
    ∃ X ∈ admissible p P ℱ B 0 x, ∀ n : ℕ, X (p.T n) =ᵐ[P] H n := by sorry

end PeriodicEval
