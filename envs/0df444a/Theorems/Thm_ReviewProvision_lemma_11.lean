-- Prove2me | Theorems.Thm_ReviewProvision_lemma_11
-- name    : ReviewProvision.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:58:04.652555+00:00
-- url     : https://prove2.me/theorems/aa6260a8-1215-4ea1-ae43-d6857aab6e24
-- title:
--   Lemma 11, p.43 — order of the variances (corrected: strict only with positive sales)
-- statement:
--   For feasible sales $\vec k$ and every cluster $n$,
--
--   $$
--   \mathrm{Var}[v_{An}]\le\mathrm{Var}[v_{Jn}],\qquad \mathrm{Var}[v_{Gn}]\le\mathrm{Var}[v_{Jn}],\qquad \mathrm{Var}[v_{Jn}]\le\mathrm{Var}[v_{Fn}].
--   $$
--
--   Moreover $\mathrm{Var}[v_{An}]<\mathrm{Var}[v_{Jn}]$ if $k_l>0$ for some $l\ne n$, and $\mathrm{Var}[v_{Gn}]<\mathrm{Var}[v_{Jn}]$ if in addition $k_n>0$.
--
--   JP sits between the partial policies and full information, and strictly above the partial ones as soon as its second signal says something new.
--
--   Differences from the source:
--   - generalization: N ≥ 2 clusters (§3.1, p.9) → every N; reason: the statement holds for every N, and N ≥ 2 is a special case
--   - correction: σ_{Jn}(~k) > σ_{An}(~k) and σ_{Jn}(~k) > σ_{Gn}(~k) for the first-period sales volume ~k → ≤ for every feasible ~k; strict with some k_l > 0, l ≠ n, and for GP also k_n > 0; reason: at τ = η = θ = ζ = 1, N = 2: ~k = (1, 0), n = 1 has no cluster 2 reviews, r̄ = r_1, σ²_{A1} = σ²_{G1} = σ²_{J1} = 4/3; ~k = (0, 1), n = 1 has σ²_{G1} = σ²_{J1} = 1/3; the proofs of the paper use k_N = 0, so these points are in the domain
--   - encoding: the formulas σ_{ψn}(~k) → Var[v_{ψn}]; reason: the closed forms are 0/0 at S_1 = 0 or S′_1 = 0; they equal the variances elsewhere (Lemma 1, (12), (13))
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), Lemma 11, p.43

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Lemma 11 (corrected: strict only with positive sales)**, SSRN 3403322 (manuscript of 2021-05-24),
p.43 (PDF 43): for feasible sales, `Var v_{An} ≤ Var v_{Jn}`, `Var v_{Gn} ≤ Var v_{Jn}`,
`Var v_{Jn} ≤ Var v_{Fn}`; `Var v_{An} < Var v_{Jn}` when some `k_l > 0`, `l ≠ n`; and
`Var v_{Gn} < Var v_{Jn}` when moreover `k_n > 0`.

**Formalization Note.** The printed strict inequalities fail at the boundary. With
`τ = η = θ = ζ = 1`, `N = 2`: at `~k = (1, 0)`, `n = 1`, no cluster 2 reviews exist, so
`r̄ = r_1` and `σ²_{A1} = σ²_{G1} = σ²_{J1} = 4/3`; at `~k = (0, 1)`, `n = 1`, `σ²_{G1} = σ²_{J1} = 1/3`.
The statement is on `Var`, not on the closed forms, so no `0/0` arises. -/
theorem lemma_11 (p : Params) {N : ℕ} (k : Fin N → ℝ) (hk : Feasible k) (n : Fin N) :
    Var[posteriorMean p k .AP n; prior p N] ≤ Var[posteriorMean p k .JP n; prior p N] ∧
    Var[posteriorMean p k .GP n; prior p N] ≤ Var[posteriorMean p k .JP n; prior p N] ∧
    Var[posteriorMean p k .JP n; prior p N] ≤ Var[posteriorMean p k .FP n; prior p N] ∧
    ((∃ l, l ≠ n ∧ 0 < k l) →
      Var[posteriorMean p k .AP n; prior p N] < Var[posteriorMean p k .JP n; prior p N]) ∧
    ((∃ l, l ≠ n ∧ 0 < k l) → 0 < k n →
      Var[posteriorMean p k .GP n; prior p N] < Var[posteriorMean p k .JP n; prior p N]) := by sorry

end ReviewProvision
