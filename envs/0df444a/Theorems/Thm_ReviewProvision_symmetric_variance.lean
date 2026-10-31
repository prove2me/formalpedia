-- Prove2me | Theorems.Thm_ReviewProvision_symmetric_variance
-- name    : ReviewProvision.symmetric_variance
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:57:52.270018+00:00
-- url     : https://prove2.me/theorems/a3a9b480-769b-43be-88da-4dba7613a397
-- title:
--   Proofs of Propositions 3 and 4, p.45 — $\sigma_F^2=\sigma_J^2$ at symmetric sales
-- statement:
--   Let $N\ge2$, $k\ge0$, sales $(k,\dots,k)$ and $w=k\theta\zeta$. For every cluster,
--
--   $$
--   \mathrm{Var}[v_{Fn}]=\mathrm{Var}[v_{Jn}]=\frac{w[N\eta^3+(\tau+\eta)(\tau+N\eta)w+\tau\eta(\tau+2\eta)]}{\tau\eta(\eta+w)[\tau\eta+(\tau+N\eta)w]},
--   $$
--
--   and this also equals
--
--   $$
--   \frac{w[N\eta^2(w+\eta)+\eta(w+Nw+2\eta)\tau+(w+\eta)\tau^2]}{\tau\eta(w+\eta)[Nw\eta+(w+\eta)\tau]}.
--   $$
--
--   At symmetric sales, the global average tells a customer as much as all the separate ratings of the other clusters.
--
--   Differences from the source:
--   - encoding: σ²_J(k), σ²_F(k) → Var[v_{Jn}], Var[v_{Fn}] at sales (k, …, k); reason: (13) is 0/0 at k = 0, where the printed common value is still right
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), proof of Proposition 4, p.45; proof of Proposition 3, p.45

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Symmetric variances**, SSRN 3403322 (manuscript of 2021-05-24), proofs of Propositions 3 and 4,
p.45 (PDF 45): at symmetric sales `k ≥ 0`, with `w = k θ ζ`,
`Var v_{Fn} = Var v_{Jn} = w[Nη³ + (τ+η)(τ+Nη)w + τη(τ+2η)]/(τη(η+w)[τη + (τ+Nη)w])`, and this equals
the second printed form `w[Nη²(w+η) + η(w+Nw+2η)τ + (w+η)τ²]/(τη(w+η)[Nwη + (w+η)τ])`.

**Formalization Note.** On `Var`, not on (12) and (13), so the formula is also valid at `k = 0`. -/
theorem symmetric_variance (p : Params) {N : ℕ} (hN : 2 ≤ N) (k : ℝ) (hk : 0 ≤ k) (n : Fin N) :
    Var[posteriorMean p (fun _ => k) .FP n; prior p N] = sigmaSqSym p N (k * p.theta * p.zeta) ∧
    Var[posteriorMean p (fun _ => k) .JP n; prior p N] = sigmaSqSym p N (k * p.theta * p.zeta) ∧
    sigmaSqSym p N (k * p.theta * p.zeta) =
      (k * p.theta * p.zeta) *
        (N * p.eta ^ 2 * ((k * p.theta * p.zeta) + p.eta) +
          p.eta * ((k * p.theta * p.zeta) + N * (k * p.theta * p.zeta) + 2 * p.eta) * p.tau +
          ((k * p.theta * p.zeta) + p.eta) * p.tau ^ 2) /
        (p.tau * p.eta * ((k * p.theta * p.zeta) + p.eta) *
          (N * (k * p.theta * p.zeta) * p.eta + ((k * p.theta * p.zeta) + p.eta) * p.tau)) := by sorry

end ReviewProvision
