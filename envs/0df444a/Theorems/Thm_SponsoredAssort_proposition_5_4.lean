-- Prove2me | Theorems.Thm_SponsoredAssort_proposition_5_4
-- name    : SponsoredAssort.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:55:53.935984+00:00
-- url     : https://prove2.me/theorems/c7bde63c-999f-4a84-86cc-91bfefb00093
-- title:
--   Proposition 5.4 — if $r_i/r_{i+1}\ge n$, then $\gamma^{PI}(r)=1/n$, achieved by $m^{\downarrow}$ (corrected: payment rule of $m^{\downarrow}$)
-- statement:
--   Let $n\ge1$ sellers have revenues $r>0$ with
--
--   $$
--   \frac{r_i}{r_{i+1}}\ \ge\ n\qquad\text{for all } i .
--   $$
--
--   Then the prior-independent competitive ratio of truthful deterministic mechanisms is
--
--   $$
--   \gamma^{PI}(r)=\frac1n ,
--   $$
--
--   and it is achieved by $m^{\downarrow}$: for every choice of a welfare-maximizing singleton at each profile, the partition mechanism $m^{\downarrow}$ of the singletons satisfies (IC) and (IR) and
--
--   $$
--   \inf_{F\in\mathcal P(\mathbb R^n_+)}\frac{\mathbb E_{v\sim F}[R(m^{\downarrow},v)]}{\mathbb E_{v\sim F}[R(m^{FB},v)]}=\frac1n .
--   $$
--
--   No ex-post truthful deterministic mechanism guarantees more than a $1/n$ fraction of first-best welfare, and displaying the best single seller already guarantees $1/n$; the social cost of truthfulness grows with the number of sellers.
--
--   Differences from the source:
--   - reading: $\gamma^{PI}(\rho)$ → $\gamma^{PI}(r)$; reason: $\rho$ is left over from the two-seller section; the ratio is that of Definition 2.2
--   - reading: $\gamma^{PI}(\rho)\le1/n$; the competitive ratio is achieved by $m^{\downarrow}$ → $\gamma^{PI}(r)=1/n$, and $m^{\downarrow}$ is IC, IR and has worst-case ratio $1/n$; reason: achieved means $m^{\downarrow}\in M$ attains $\gamma^{PI}(r)$; with the bound $\ge1/n$ of p.28 this is the equality
--   - encoding: expectations; infimum over all $F\in\mathcal P(\mathbb R^n_+)$ → lower Lebesgue integrals in $[0,\infty]$; the prior $\delta_0$ excluded; reason: $\delta_0$ gives $0/0$; the integrals agree with expectations for measurable integrands and impose no measurability on mechanisms
--   - encoding: sellers $1,\dots,n$; $r_i/r_{i+1}\ge n$ → `Fin n`; $n\,r_{i+1}\le r_i$; reason: 0-based indexing; equivalent for $r>0$
--   - generalization: payments $p_i\ge0$ (step 3, p.9) → real-valued payments, as in $p:\mathbb R^n_+\to\mathbb R^n$ (p.10); reason: a larger $M$ makes the upper bound stronger; $m^{\downarrow}$'s payments are nonnegative
--   - generalization: $m^{\downarrow}$ with the $\arg\max$ ties unresolved → every welfare-maximizing selector; reason: holds for every tie-breaking rule
--   - correction: $m^{\downarrow}$ with payment (3) → payment by the rule after (3); reason: with (3), $m^{\downarrow}$ violates (IR) at $r=(2,1)$ (which satisfies $r_1/r_2\ge n=2$), $v=(1/3,1)$, so the printed $m^{\downarrow}$ is not in $M$
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Proposition 5.4, p.28 (proof: Appendix G.3, OA pp.38–39)

import Mathlib
import Definitions.Def_SponsoredAssort_gammaPI
import Definitions.Def_SponsoredAssort_IsBestSelector
import Definitions.Def_SponsoredAssort_partitionMech
import Definitions.Def_SponsoredAssort_singletons

open scoped NNReal ENNReal

namespace SponsoredAssort

/-- **Proposition 5.4** (Balseiro, Désir, *Incentive-Compatible Assortment Optimization for
Sponsored Products*, SSRN 3821382 (Feb. 21, 2022), p.28). Let `n ≥ 1` sellers have revenues
`r > 0` with `rᵢ/rᵢ₊₁ ≥ n` for all `i`. Then the prior-independent competitive ratio satisfies
`γ^PI(r) ≤ 1/n`, and the ratio is achieved by `m↓`: for every pointwise welfare-maximizing
selector over the singletons, the partition mechanism `m↓` is (IC) and (IR) and its worst-case
ratio over priors equals `γ^PI(r) = 1/n`.

**Formalization Note.** `γ^PI(ρ)` in the printed statement is `γ^PI(r)` of Definition 2.2.
"Achieved by `m↓`" is read as: `m↓ ∈ M` and its worst-case ratio is `γ^PI(r)`; with the paper's
bound `≥ 1/n` for `m↓` (p.28) this gives `γ^PI(r) = 1/n`, which is stated. Sellers are 0-based,
`rᵢ/rᵢ₊₁ ≥ n` is `n·rᵢ₊₁ ≤ rᵢ` (it implies `r₁ ≥ ⋯ ≥ rₙ` for `n ≥ 2`). Expectations are lower
Lebesgue integrals, so `M` carries no measurability condition; the prior `δ₀` (ratio `0/0`) is
excluded; payments are real-valued; `m↓` charges by the rule after (3) (see `partitionMech`). -/
theorem proposition_5_4 {n : ℕ} [NeZero n] (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hratio : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → (n : ℝ) * r j ≤ r i) :
    gammaPI r = 1 / (n : ℝ≥0∞) ∧
    ∀ S : Attr n → Finset (Fin n), IsBestSelector r (singletons n) S →
      IsIC r (partitionMech r (singletons n) S) ∧
      IsIR r (partitionMech r (singletons n) S) ∧
      worstCaseRatio r (partitionMech r (singletons n) S) = 1 / (n : ℝ≥0∞) := by sorry

end SponsoredAssort
