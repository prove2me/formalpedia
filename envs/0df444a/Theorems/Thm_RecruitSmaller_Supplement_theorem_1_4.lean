-- Prove2me | Theorems.Thm_RecruitSmaller_Supplement_theorem_1_4
-- name    : RecruitSmaller.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:59:02.884077+00:00
-- url     : https://prove2.me/theorems/0233bf73-deac-4c0c-be9c-0de0bf9426d0
-- title:
--   Theorem 1.4 — fewer than $\max(2,\lceil1/r\rceil-1)$ extra sellers never suffice under $r$-dominance
-- statement:
--   Let $r\in(0,1]$ and let $c\ge1$ be an integer with
--   $$
--   c<\max\big(2,\lceil1/r\rceil-1\big).
--   $$
--   Let $M$ be any prior-independent mechanism (deterministic or randomized) for $m=1$ buyer and $k=1+c$ sellers that is DSIC, IR and WBB. Then there exist distributions $F_B\succeq_r F_S$ on $[0,1]$ (that is, $1-F_B(x)\ge r(1-F_S(x))$ for all $x$) with $\mathrm{OPT}(1,1)>0$ such that
--   $$
--   \mathrm{GFT}_M(1,1+c)<\mathrm{OPT}(1,1). \tag{1.4}
--   $$
--   Here a **mechanism** for $m$ buyers and $k$ sellers assigns to every reported profile $(b,s)\in\mathbb R^m\times\mathbb R^k$ measurable expected allocation probabilities $x^B_j(b,s),x^S_\ell(b,s)\in[0,1]$ with $\sum_j x^B_j=\sum_\ell x^S_\ell$, and expected payments $p^B_j,p^S_\ell\in\mathbb R$; DSIC, IR and WBB are the dominant-strategy, ex-post and pointwise notions of §2.1, and $\mathrm{GFT}_M(m,k)$ is the expectation of $\sum_j b_jx^B_j-\sum_\ell s_\ell x^S_\ell$ under $F_B^m\times F_S^k$.
--
--   With Theorem 1.3, this pins the competition complexity of the smaller side under $r$-dominance to within two traders.
--
--   Differences from the source:
--   - encoding: distributions (CDFs) on [0, 1] → probability measures μ on ℝ with μ [0, 1] = 1, CDF cdf μ; reason: every distribution on [0, 1] is exactly one such measure; same instances
--   - encoding: prior-independent mechanism (rules do not depend on F_B, F_S) → ∀ M, ∃ μB μS (the mechanism is quantified before the distributions); reason: a mechanism is a fixed function of the reports, so the quantifier order is prior independence
--   - encoding: randomized mechanism given by expected allocations and payments (§2.1) → structure Mechanism with expected allocations in [0, 1], feasibility Σ xB = Σ xS, jointly measurable allocations, real payments; reason: the page defines a mechanism by exactly these expected quantities; deterministic mechanisms are the {0,1}-valued case
--   - encoding: GFT_M < OPT with OPT a real expectation → OPT ≠ ⊤ ∧ Integrable gft_M ∧ GFT_M < OPT.toReal, with OPT the published ℝ≥0∞-valued RecruitSmaller.OPT and GFT_M a Bochner integral; reason: both clauses are automatic for laws on [0, 1] with measurable allocations in [0, 1]; stated so the Bochner and toReal junk values cannot make the comparison vacuous
--   - encoding: ⌈1/r⌉ (integer ceiling) → Nat.ceil ⌈1/r⌉₊; reason: 1/r ≥ 1 > 0, so the natural and integer ceilings agree
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Theorem 1.4, p.3 (PDF 5), eq. (1.4)

import Mathlib
import Definitions.Def_RecruitSmaller_OPT
import Definitions.Def_RecruitSmaller_Supplement_IsDSIC
import Definitions.Def_RecruitSmaller_Supplement_IsIR
import Definitions.Def_RecruitSmaller_Supplement_IsWBB
import Definitions.Def_RecruitSmaller_Supplement_GFT__8e3ec3

open MeasureTheory ProbabilityTheory

namespace RecruitSmaller.Supplement

/-- **Theorem 1.4 (Mechanism-Independent Lower Bound for Recruiting the Smaller Side)**
(Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.3, eq. (1.4); proof Appendix C.2): let `r ∈ (0, 1]` and let `c ∈ ℤ_{≥1}` satisfy
`c < max(2, ⌈1/r⌉ − 1)`. Let `M` be any prior-independent mechanism (deterministic or randomized)
for `m = 1` buyer and `k = 1 + c` sellers that is DSIC, IR and WBB. Then there exist distributions
`F_B ⪰_r F_S` on `[0, 1]` (i.e. `1 − F_B(x) ≥ r(1 − F_S(x))` for all `x`) with `OPT(1, 1) > 0`
such that `GFT_M(1, 1 + c) < OPT(1, 1)`.

**Formalization Note** "Distributions on [0, 1]" are probability measures `μ` on `ℝ` with
`μ [0, 1] = 1`, with CDFs `F = cdf μ`. Prior independence is the quantifier order: the mechanism is
fixed first and the distributions are chosen afterwards. `OPT` is the published `RecruitSmaller.OPT`
(valued in `ℝ≥0∞`); the conclusion also asserts `OPT(1, 1) < ∞` and the integrability of `gft_M`
(both automatic on `[0, 1]`) so that the comparison of the real `GFT_M` with `OPT.toReal` is the
page's comparison. `⌈1/r⌉` is `Nat.ceil`; since `1/r ≥ 1`, the natural-number difference `⌈1/r⌉₊ − 1` is the
page's integer `⌈1/r⌉ − 1`. -/
theorem theorem_1_4 (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) (c : ℕ) (hc1 : 1 ≤ c)
    (hc : c < max 2 (⌈1 / r⌉₊ - 1))
    (M : Mechanism 1 (1 + c)) (hDSIC : IsDSIC M) (hIR : IsIR M) (hWBB : IsWBB M) :
    ∃ μB μS : Measure ℝ, IsProbabilityMeasure μB ∧ IsProbabilityMeasure μS ∧
      μB (Set.Icc 0 1) = 1 ∧ μS (Set.Icc 0 1) = 1 ∧
      (∀ x, r * (1 - cdf μS x) ≤ 1 - cdf μB x) ∧
      0 < OPT 1 1 μB μS ∧ OPT 1 1 μB μS ≠ ⊤ ∧
      Integrable (fun ω : (Fin 1 → ℝ) × (Fin (1 + c) → ℝ) => gft M ω.1 ω.2)
        ((Measure.pi fun _ : Fin 1 => μB).prod (Measure.pi fun _ : Fin (1 + c) => μS)) ∧
      GFT M μB μS < (OPT 1 1 μB μS).toReal := by sorry

end RecruitSmaller.Supplement
