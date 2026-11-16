-- Prove2me | Theorems.Thm_RecruitSmaller_Supplement_theorem_1_2
-- name    : RecruitSmaller.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:57:20.219515+00:00
-- url     : https://prove2.me/theorems/3cbd179d-3c93-4645-8f81-eb86f2be4449
-- title:
--   Theorem 1.2 (One Trader is Insufficient) — no DSIC, IR, WBB mechanism with one extra seller beats $\mathrm{OPT}(1,1)$
-- statement:
--   Let $M$ be any prior-independent mechanism (deterministic or randomized) for $m=1$ buyer and $k=2$ sellers that is dominant-strategy incentive compatible (DSIC), individually rational (IR) and weakly budget-balanced (WBB). Then there exist distributions $F_B\succeq_{\mathrm{FSD}}F_S$ on $[0,1]$ (that is, $F_B(x)\le F_S(x)$ for all $x$) with $\mathrm{OPT}(1,1)>0$ such that
--   $$
--   \mathrm{GFT}_M(1,2)<\mathrm{OPT}(1,1). \tag{1.2}
--   $$
--   Here a **mechanism** for $m$ buyers and $k$ sellers assigns to every reported profile $(b,s)\in\mathbb R^m\times\mathbb R^k$ measurable expected allocation probabilities $x^B_j(b,s),x^S_\ell(b,s)\in[0,1]$ with $\sum_j x^B_j=\sum_\ell x^S_\ell$, and expected payments $p^B_j,p^S_\ell\in\mathbb R$; DSIC, IR and WBB are the dominant-strategy, ex-post and pointwise notions of §2.1, and $\mathrm{GFT}_M(m,k)$ is the expectation of $\sum_j b_jx^B_j-\sum_\ell s_\ell x^S_\ell$ under $F_B^m\times F_S^k$. $\mathrm{OPT}(1,1)$ is the expected first-best Gains From Trade of one buyer and one seller.
--
--   Together with Theorem 1.1, this shows that two recruited sellers is the exact competition complexity of the smaller side under first-order stochastic dominance.
--
--   **Formalization Note** The conclusion also records $\mathrm{OPT}(1,1)<\infty$ and the integrability of $\mathrm{gft}_M$, both automatic for laws on $[0,1]$.
--
--   Differences from the source:
--   - encoding: distributions (CDFs) on [0, 1] → probability measures μ on ℝ with μ [0, 1] = 1, CDF cdf μ; reason: every distribution on [0, 1] is exactly one such measure; same instances
--   - encoding: prior-independent mechanism (rules do not depend on F_B, F_S) → ∀ M, ∃ μB μS (the mechanism is quantified before the distributions); reason: a mechanism is a fixed function of the reports, so the quantifier order is prior independence
--   - encoding: randomized mechanism given by expected allocations and payments (§2.1) → structure Mechanism with expected allocations in [0, 1], feasibility Σ xB = Σ xS, jointly measurable allocations, real payments; reason: the page defines a mechanism by exactly these expected quantities; deterministic mechanisms are the {0,1}-valued case
--   - encoding: GFT_M < OPT with OPT a real expectation → OPT ≠ ⊤ ∧ Integrable gft_M ∧ GFT_M < OPT.toReal, with OPT the published ℝ≥0∞-valued RecruitSmaller.OPT and GFT_M a Bochner integral; reason: both clauses are automatic for laws on [0, 1] with measurable allocations in [0, 1]; stated so the Bochner and toReal junk values cannot make the comparison vacuous
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Theorem 1.2, p.2 (PDF 4), eq. (1.2)

import Mathlib
import Definitions.Def_RecruitSmaller_OPT
import Definitions.Def_RecruitSmaller_Supplement_IsDSIC
import Definitions.Def_RecruitSmaller_Supplement_IsIR
import Definitions.Def_RecruitSmaller_Supplement_IsWBB
import Definitions.Def_RecruitSmaller_Supplement_GFT__8e3ec3

open MeasureTheory ProbabilityTheory

namespace RecruitSmaller.Supplement

/-- **Theorem 1.2 (One Trader is Insufficient)** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.2, eq. (1.2); proof §4 and Appendix B):
let `M` be any prior-independent mechanism (deterministic or randomized) for `m = 1` buyer and
`k = 2` sellers that is DSIC, IR and WBB. Then there exist distributions `F_B ⪰_FSD F_S` on
`[0, 1]` with `OPT(1, 1) > 0` such that `GFT_M(1, 2) < OPT(1, 1)`.

**Formalization Note** "Distributions on [0, 1]" are probability measures `μ` on `ℝ` with
`μ [0, 1] = 1`, with CDFs `F = cdf μ`. Prior independence is the quantifier order: the mechanism is
fixed first and the distributions are chosen afterwards. `OPT` is the published `RecruitSmaller.OPT`
(valued in `ℝ≥0∞`); the conclusion also asserts `OPT(1, 1) < ∞` and the integrability of `gft_M`
(both automatic on `[0, 1]`) so that the comparison of the real `GFT_M` with `OPT.toReal` is the
page's comparison. -/
theorem theorem_1_2 (M : Mechanism 1 2) (hDSIC : IsDSIC M) (hIR : IsIR M) (hWBB : IsWBB M) :
    ∃ μB μS : Measure ℝ, IsProbabilityMeasure μB ∧ IsProbabilityMeasure μS ∧
      μB (Set.Icc 0 1) = 1 ∧ μS (Set.Icc 0 1) = 1 ∧
      (∀ x, cdf μB x ≤ cdf μS x) ∧
      0 < OPT 1 1 μB μS ∧ OPT 1 1 μB μS ≠ ⊤ ∧
      Integrable (fun ω : (Fin 1 → ℝ) × (Fin 2 → ℝ) => gft M ω.1 ω.2)
        ((Measure.pi fun _ : Fin 1 => μB).prod (Measure.pi fun _ : Fin 2 => μS)) ∧
      GFT M μB μS < (OPT 1 1 μB μS).toReal := by sorry

end RecruitSmaller.Supplement
