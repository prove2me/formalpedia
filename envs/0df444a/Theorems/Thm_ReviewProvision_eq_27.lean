-- Prove2me | Theorems.Thm_ReviewProvision_eq_27
-- name    : ReviewProvision.eq_27
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:58:20.284032+00:00
-- url     : https://prove2.me/theorems/31d2162e-71aa-4834-908b-5f7f31fb2f50
-- title:
--   Eq. (27), p.45 — first-order conditions of FP
-- statement:
--   Let $\vec k$ be optimal for FP, $w_l=k_l\theta\zeta$, and $\sigma_l=\sigma_{Fl}(\vec k)$. Then $k_n>0$ for every cluster, and
--
--   $$
--   k_n=\frac12+\frac{m\theta\zeta}{8}\sum_{l=1}^Ng(\sigma_l)\frac{\partial\sigma_l^2}{\partial w_n}\qquad\text{for all }n .
--   $$
--
--   An FP optimum is thus interior, and it is characterized by these equations.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - encoding: the clusters ordered k*_{F1} ≥ … ≥ k*_{FN} > 0 → every cluster n, without the ordering; reason: the ordering on p.44 is a relabelling of the clusters
--   - encoding: σ_l = σ_{Fl}(~k) → the square root of the closed form (12); reason: (12) is the variance by eq_12; it is positive at an optimum
--   - reading: the feasible sales are not stated → k_n ≥ 0 for all n, with no upper bound; reason: the proofs use k_N ≥ 0 and evaluate at k_N = 0 (pp.37, 44); (27) has no multiplier, and an upper bound k_n ≤ 1 is not intended since the optimum can exceed 1
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), eq. (27), p.45

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Eq. (27)**, SSRN 3403322 (manuscript of 2021-05-24), p.45 (PDF 45): an optimum of FP has positive
sales and satisfies the first-order conditions
`k_n = 1/2 + (mθζ/8) Σ_l g(σ_l) ∂σ²_l/∂w_n`, with `σ_l = σ_{Fl}(~k)`.

**Formalization Note.** The page orders clusters by `k_1 ≥ … ≥ k_N` without loss of generality; the
statement is for every cluster. `σ_l` is the square root of the closed form (12), positive here. -/
theorem eq_27 (p : Params) {N : ℕ} (k : Fin N → ℝ) (hk : IsOptimal p .FP k) (n : Fin N) :
    0 < k n ∧
    k n = 1 / 2 + p.m * p.theta * p.zeta / 8 *
      ∑ l, g √(sigmaSqF p (weight p k) l) * dSigmaSqF p (weight p k) l n := by sorry

end ReviewProvision
