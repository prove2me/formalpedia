-- Prove2me | Theorems.Thm_RecruitSmaller_Supplement_theorem_1_3
-- name    : RecruitSmaller.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:58:16.777589+00:00
-- url     : https://prove2.me/theorems/cdb33613-4f48-40cb-9a91-f4768ed434e4
-- title:
--   Theorem 1.3 — $\mathrm{STR}(m,n+\lceil1/r\rceil+1)\ge\mathrm{OPT}(m,n)$ under $r$-dominance
-- statement:
--   Let $r\in(0,1]$ and let $m,n$ be integers with $m\ge n\ge1$. Let $F_B$ and $F_S$ be cumulative distribution functions on $\mathbb R$ such that $F_B$ $r$-dominates $F_S$,
--   $$
--   1-F_B(x)\ge r\,\big(1-F_S(x)\big)\qquad\text{for all }x\in\mathbb R,
--   $$
--   and $\mathrm{OPT}(m,n)<\infty$. Then recruiting $c=\lceil1/r\rceil+1$ additional sellers drawn independently from $F_S$ suffices for Seller Trade Reduction to match or exceed the first-best Gains From Trade of the original market:
--   $$
--   \mathrm{STR}\big(m,n+\lceil1/r\rceil+1\big)\ge\mathrm{OPT}(m,n). \tag{1.3}
--   $$
--   At $r=1$ this is Theorem 1.1. No continuity or support assumption is made on $F_B$ or $F_S$.
--
--   Differences from the source:
--   - encoding: CDFs F_B, F_S on ℝ → probability measures μB, μS on ℝ with F = cdf μ; reason: every CDF on ℝ is the CDF of exactly one probability measure; same instances
--   - encoding: expected Gains From Trade as real expectations with OPT(m, n) < ∞ → published ℝ≥0∞-valued OPT and STR, with OPT m n μB μS ≠ ⊤; reason: both integrands are nonnegative; same values, ∞ representable
--   - encoding: ⌈1/r⌉ (integer ceiling) → Nat.ceil ⌈1/r⌉₊; reason: 1/r ≥ 1 > 0, so the natural and integer ceilings agree
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Theorem 1.3, p.3 (PDF 5), eq. (1.3); Definition 2.2, eq. (2.1), p.10

import Mathlib
import Definitions.Def_RecruitSmaller_OPT
import Definitions.Def_RecruitSmaller_STR

open MeasureTheory ProbabilityTheory

namespace RecruitSmaller.Supplement

/-- **Theorem 1.3 (Recruiting the Smaller Side under r-Dominance)** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.3, eq. (1.3); proof §5
and Appendix C.1): let `r ∈ (0, 1]` and `m, n ∈ ℤ_{≥1}` with `m ≥ n`. Let `F_B`, `F_S` be
cumulative distribution functions on `ℝ` with `F_B ⪰_r F_S`, i.e. `1 − F_B(x) ≥ r(1 − F_S(x))` for
all `x ∈ ℝ` (Definition 2.2, eq. (2.1)), and `OPT(m, n) < ∞`. Then
`STR(m, n + ⌈1/r⌉ + 1) ≥ OPT(m, n)`.

**Formalization Note** As in the published `RecruitSmaller.theorem_1_1`: distributions are
probability measures on `ℝ` with CDFs `cdf μ`; `OPT` and `STR` are the published expected Gains
From Trade in `ℝ≥0∞`; no continuity or support assumption. `⌈1/r⌉` is `Nat.ceil` (`1/r ≥ 1 > 0`). -/
theorem theorem_1_3 (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) (m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (μB μS : Measure ℝ) [IsProbabilityMeasure μB] [IsProbabilityMeasure μS]
    (hdom : ∀ x, r * (1 - cdf μS x) ≤ 1 - cdf μB x) (hOPT : OPT m n μB μS ≠ ⊤) :
    OPT m n μB μS ≤ STR m (n + ⌈1 / r⌉₊ + 1) μB μS := by sorry

end RecruitSmaller.Supplement
