-- Prove2me | Theorems.Thm_TradeAgentNV_lemma_2
-- name    : TradeAgentNV.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:29:38.161214+00:00
-- url     : https://prove2.me/theorems/6e593d5c-e6a4-481c-a81c-efc561e48d2f
-- title:
--   Lemma 2: $E[\min(U,s)]/E[U]>s$ for a continuous yield with $E[U]<1$
-- statement:
--   Let $U$ be a random variable with $0\le U\le1$ almost surely and no atoms ($P(U=x)=0$ for every $x$), and suppose $E[U]<1$. Then for every $s\in(0,1)$,
--   $$
--   \frac{E[\min(U,s)]}{E[U]}>s .
--   $$
--   The paper uses it to compare the expected sales-to-supply ratio with its threshold.
--
--   Differences from the source:
--   - generalization: $U$ has support $[0,1]$ → $U\in[0,1]$ almost surely (support contained in $[0,1]$); reason: every $U$ with support $[0,1]$ satisfies it, so the statement specializes to the source
--   - encoding: $U$ is a continuous random variable → $P(U=x)=0$ for every real $x$; reason: a continuous random variable is one with a continuous cdf, i.e. without atoms
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, Appendix A, Lemma 2, p.28

import Mathlib

open MeasureTheory

namespace TradeAgentNV

/-- **Lemma 2** (Appendix A, p.28) of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023): let `U` be a continuous
random variable with values in `[0, 1]`. If `E[U] < 1`, then `E[min(U, s)]/E[U] > s` for every
`s ∈ (0, 1)`.

**Formalization Note.** "Continuous" is encoded as "no atoms": `P(U = x) = 0` for every `x`.
"Support `[0, 1]`" is weakened to `U ∈ [0, 1]` almost surely (the support is contained in
`[0, 1]`); this covers the paper's case. `E[U] > 0` follows from the hypotheses (no atom at
`0`), so the quotient has a positive denominator. -/
theorem lemma_2
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U)
    (hU01 : ∀ᵐ ω ∂P, U ω ∈ Set.Icc (0 : ℝ) 1) (hcont : ∀ x : ℝ, P {ω | U ω = x} = 0)
    (hEU1 : ∫ ω, U ω ∂P < 1) :
    ∀ s : ℝ, 0 < s → s < 1 → s < (∫ ω, min (U ω) s ∂P) / ∫ ω, U ω ∂P := by sorry

end TradeAgentNV
