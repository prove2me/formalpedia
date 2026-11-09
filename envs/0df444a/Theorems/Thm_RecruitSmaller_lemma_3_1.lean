-- Prove2me | Theorems.Thm_RecruitSmaller_lemma_3_1
-- name    : RecruitSmaller.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:01.182671+00:00
-- url     : https://prove2.me/theorems/0bf48571-b4e2-4df1-8bbf-252d0b99eb68
-- title:
--   Lemma 3.1 — $\mathrm{STR}(m,n+2)-\mathrm{OPT}(m,n)\ge\sum_{i=1}^n\int I_i(x)\,dx$
-- statement:
--   Let $m\ge n\ge1$ and let $F_B,F_S$ be any distributions on $\mathbb R$ with $\mathrm{OPT}(m,n)<\infty$. Then
--   $$
--   \mathrm{STR}(m,n+2)-\mathrm{OPT}(m,n)\ \ge\ \sum_{i=1}^{n}\int_{-\infty}^{\infty}I_i(x)\,dx, \tag{3.1}
--   $$
--   where for each rank $i\in\{1,\dots,n\}$ and threshold $x$ with $p:=F_S(x)$,
--   $$
--   I_i(x)=p^i\,\mathbb E_{b^{(i)}}\Bigl[\Bigl(A_{n,i}(p)-\binom{n+2}{i}\bigl(1-F_S(b^{(i)})\bigr)^{n+2-i}\Bigr)\mathbb 1\bigl[b^{(i)}\ge x\bigr]\Bigr] \tag{3.2}
--   $$
--   and $A_{n,i}$ is as in (3.3). The statement also asserts that each $I_i$ is Lebesgue integrable on $\mathbb R$.
--
--   The lemma reduces Theorem 1.1 to the pointwise inequality $I_i(x)\ge0$ for every rank and threshold. No distributional assumption beyond $\mathrm{OPT}(m,n)<\infty$ is made.
--
--   **Formalization Note** Since $\mathrm{STR}(m,n+2)$ may a priori be infinite, the inequality is stated in the extended reals as $\mathrm{OPT}(m,n)+\sum_i\int I_i\le\mathrm{STR}(m,n+2)$.
--
--   Differences from the source:
--   - encoding: STR(m, n+2) − OPT(m, n) ≥ Σᵢ ∫ Iᵢ → OPT(m, n) + Σᵢ ∫ Iᵢ ≤ STR(m, n+2) in EReal; reason: OPT(m, n) is finite, so the two forms are equivalent, and STR(m, n+2) = ∞ is representable
--   - generalization: ∫ Iᵢ(x) dx presupposed to exist → each Iᵢ asserted Lebesgue integrable; reason: the page's integral presupposes it (it follows from Lemmas 3.3–3.5); dropping the clause gives the page's inequality
--   - encoding: distributions with CDFs F_B, F_S on ℝ → probability measures μB, μS on ℝ with F_B = cdf μB, F_S = cdf μS; reason: every CDF on ℝ is the CDF of exactly one probability measure; same instances
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.1, pp.11–12, eqs. (3.1)–(3.3)

import Mathlib
import Definitions.Def_RecruitSmaller_OPT
import Definitions.Def_RecruitSmaller_STR
import Definitions.Def_RecruitSmaller_I

open MeasureTheory

namespace RecruitSmaller

/-- **Lemma 3.1** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), pp.11–12, eqs. (3.1)–(3.3)): let `m ≥ n ≥ 1` and let
`F_B`, `F_S` be any distributions on `ℝ` with `OPT(m, n) < ∞`. Then
`STR(m, n + 2) − OPT(m, n) ≥ ∑_{i=1}^n ∫_{−∞}^{∞} Iᵢ(x) dx`.

**Formalization Note** `STR(m, n + 2)` may a priori be `∞`, so the inequality is stated in `EReal`
as `OPT(m, n) + ∑ᵢ ∫ Iᵢ ≤ STR(m, n + 2)`, equivalent to the printed difference since `OPT(m, n)` is
finite. The statement also asserts that each `Iᵢ` is Lebesgue integrable, which the page's
`∫ Iᵢ(x) dx` presupposes. -/
theorem lemma_3_1 (m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (μB μS : Measure ℝ) [IsProbabilityMeasure μB] [IsProbabilityMeasure μS]
    (hOPT : OPT m n μB μS ≠ ⊤) :
    (∀ i ∈ Finset.Icc 1 n, Integrable (I m n μB μS i)) ∧
      (OPT m n μB μS : EReal) + ∑ i ∈ Finset.Icc 1 n, ((∫ x, I m n μB μS i x : ℝ) : EReal) ≤
        (STR m (n + 2) μB μS : EReal) := by sorry

end RecruitSmaller
