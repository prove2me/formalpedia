-- Prove2me | Theorems.Thm_RecruitSmaller_theorem_1_1
-- name    : RecruitSmaller.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:36.799208+00:00
-- url     : https://prove2.me/theorems/25bf5718-017e-4e71-9e95-d4c5139fb5af
-- title:
--   Theorem 1.1 (Two Traders Suffice) — $\mathrm{STR}(m,n+2)\ge\mathrm{OPT}(m,n)$ under FSD
-- statement:
--   Let $m,n$ be integers with $m\ge n\ge1$. Let $F_B$ and $F_S$ be cumulative distribution functions on $\mathbb R$ with $\mathrm{OPT}(m,n)<\infty$ such that $F_B$ first-order stochastically dominates $F_S$, i.e.
--   $$
--   F_B(x)\le F_S(x)\qquad\text{for all }x\in\mathbb R.
--   $$
--   Then recruiting two additional sellers drawn independently from $F_S$ suffices for Seller Trade Reduction to match or exceed the first-best Gains From Trade of the original market:
--   $$
--   \mathrm{STR}(m,n+2)\ \ge\ \mathrm{OPT}(m,n). \tag{1.1}
--   $$
--   Here $\mathrm{OPT}(m,n)$ is the expected first-best Gains From Trade with $m$ buyers (values i.i.d. $F_B$) and $n$ sellers (costs i.i.d. $F_S$), and $\mathrm{STR}(m,n+2)$ is the expected Gains From Trade of the prior-independent Seller Trade Reduction mechanism with $m$ buyers and $n+2$ sellers. No continuity or support assumption is made on $F_B$ or $F_S$.
--
--   **Formalization Note** Expectations are Lebesgue integrals in $[0,\infty]$, so the finiteness $\mathrm{OPT}(m,n)<\infty$ is a hypothesis $\mathrm{OPT}(m,n)\ne\infty$.
--
--   Differences from the source:
--   - encoding: distributions with CDFs F_B, F_S on ℝ → probability measures μB, μS on ℝ with F_B = cdf μB, F_S = cdf μS; reason: every CDF on ℝ is the CDF of exactly one probability measure; same instances
--   - encoding: expected Gains From Trade as real expectations with OPT(m, n) < ∞ → lower Lebesgue integrals in ℝ≥0∞ of nonnegative integrands, with OPT m n μB μS ≠ ⊤; reason: both integrands are nonnegative, so the extended-valued expectation is the page's expectation and ∞ is representable
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Theorem 1.1, p.2 (PDF 4), eq. (1.1)

import Mathlib
import Definitions.Def_RecruitSmaller_OPT
import Definitions.Def_RecruitSmaller_STR

open MeasureTheory ProbabilityTheory

namespace RecruitSmaller

/-- **Theorem 1.1 (Two Traders Suffice)** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.2, eq. (1.1)): let `m, n ∈ ℤ_{≥1}`
with `m ≥ n`, and let `F_B`, `F_S` be cumulative distribution functions on `ℝ` with `OPT(m, n) < ∞`
such that `F_B(x) ≤ F_S(x)` for all `x ∈ ℝ`. Then `STR(m, n + 2) ≥ OPT(m, n)`.

**Formalization Note** A distribution with CDF `F` is a probability measure `μ` on `ℝ` with
`F = cdf μ`. `OPT` and `STR` are the expected Gains From Trade of Definitions 2.3–2.4 under the
i.i.d. product laws, valued in `ℝ≥0∞`. No continuity or support assumption is made. -/
theorem theorem_1_1 (m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (μB μS : Measure ℝ) [IsProbabilityMeasure μB] [IsProbabilityMeasure μS]
    (hFSD : ∀ x, cdf μB x ≤ cdf μS x) (hOPT : OPT m n μB μS ≠ ⊤) :
    OPT m n μB μS ≤ STR m (n + 2) μB μS := by sorry

end RecruitSmaller
