-- Prove2me | Theorems.Thm_RecruitSmaller_lemma_3_8
-- name    : RecruitSmaller.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:48.685302+00:00
-- url     : https://prove2.me/theorems/43996f1a-ebb5-4d51-ae65-dd44d23ae93f
-- title:
--   Lemma 3.8 — $I_i(x)\ge p^i\int_0^{1-q_x}\psi_{n,i}(w;p)f_{i,m}(w)\,dw$ under FSD
-- statement:
--   Suppose $m\ge n\ge1$ and $F_B\succeq_{\mathrm{FSD}}F_S$, i.e. $F_B(x)\le F_S(x)$ for all $x\in\mathbb R$. Then for every rank $i\in\{1,\dots,n\}$ and every threshold $x\in\mathbb R$ with $p:=F_S(x)$ and $q_x:=F_B(x-)$, the quantity $I_i(x)$ of (3.2) satisfies
--   $$
--   I_i(x)\ \ge\ p^i\int_0^{1-q_x}\psi_{n,i}(w;p)\,f_{i,m}(w)\,dw, \tag{3.12}
--   $$
--   where $\psi_{n,i}(w;p)=A_{n,i}(p)-\binom{n+2}{i}\min(1-p,w)^{n+2-i}$ is the truncated integrand (3.10) and $f_{i,m}(w)=m\binom{m-1}{i-1}w^{i-1}(1-w)^{m-i}$ is the Beta$(i,m-i+1)$ density on $(0,1)$.
--
--   The bound moves $I_i(x)$ to quantile space for arbitrary distributions, with $m$ buyers instead of $n$.
--
--   Differences from the source:
--   - encoding: q_x := F_B(x−) → (μB (Iio x)).toReal; reason: F_B(x−) = μB((−∞, x)) for a probability measure; same value
--   - encoding: distributions with CDFs F_B, F_S on ℝ → probability measures μB, μS on ℝ with F_B = cdf μB, F_S = cdf μS; reason: every CDF on ℝ is the CDF of exactly one probability measure; same instances
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.8, p.15, eq. (3.12); proof p.27

import Mathlib
import Definitions.Def_RecruitSmaller_I
import Definitions.Def_RecruitSmaller_psi
import Definitions.Def_RecruitSmaller_betaDens

open MeasureTheory ProbabilityTheory

namespace RecruitSmaller

/-- **Lemma 3.8** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.15, eq. (3.12); proof p.27): suppose `m ≥ n ≥ 1` and
`F_B ⪰_FSD F_S`. Then for every rank `i ∈ {1, …, n}` and every threshold `x ∈ ℝ` with
`p := F_S(x)` and `q_x := F_B(x−)`, `Iᵢ(x) ≥ pⁱ ∫₀^{1−q_x} ψ_{n,i}(w; p) f_{i,m}(w) dw`, where
`f_{i,m}` is the Beta(i, m − i + 1) density.

**Formalization Note** FSD is `∀ x, cdf μB x ≤ cdf μS x` (Definition 2.2); `q_x = μB((−∞, x))`. -/
theorem lemma_3_8 (m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (μB μS : Measure ℝ) [IsProbabilityMeasure μB] [IsProbabilityMeasure μS]
    (hFSD : ∀ x, cdf μB x ≤ cdf μS x) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (x : ℝ) :
    (cdf μS x) ^ i * ∫ w in (0 : ℝ)..(1 - (μB (Set.Iio x)).toReal),
        psi n i (cdf μS x) w * betaDens m i w ≤ I m n μB μS i x := by sorry

end RecruitSmaller
