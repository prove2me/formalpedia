-- Prove2me | Theorems.Thm_PrettyGoodCriterion_Supplement_theorem_2
-- name    : PrettyGoodCriterion.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:32:37.909862+00:00
-- url     : https://prove2.me/theorems/96d156d6-5a6d-4a3a-9697-60ce54e38450
-- title:
--   Theorem 2 — MQC improvement over the first MRRW bound: $R_2(\delta)\le R_{\mathrm{MQC}}(\delta)<R_{\mathrm{MRRW}}(\delta)$
-- statement:
--   Let $h$ be the base-2 binary entropy, $s(D)=h\big((1-\sqrt{1-D})/2\big)$, and let $R_2(\delta)=\limsup_{n\to\infty}\frac1n\log_2A_2(n,\lceil\delta n\rceil)$ be the asymptotic rate function of binary codes, $A_2(n,d)$ being the largest size of a binary code of length $n$ and minimum distance at least $d$. Define
--   $$
--   R_{\mathrm{MQC}}(\delta):=\min_{0\le r\le\delta}\Big[s\big((1-2r)^2\big)-s\big(2(\delta-r)(1-2r)\big)\Big],\qquad R_{\mathrm{MRRW}}(\delta):=h\!\left(\tfrac12-\sqrt{\delta(1-\delta)}\right).
--   $$
--   Then for every $\delta\in(0,\tfrac12)$,
--   $$
--   R_2(\delta)\ \le\ R_{\mathrm{MQC}}(\delta)\ <\ R_{\mathrm{MRRW}}(\delta).
--   $$
--
--   The first inequality comes from applying the pretty good criterion (Theorem 1) to a family of mixed-qubit channels. The second says that this qubit-output channel family beats the first MRRW bound strictly at every relative distance in $(0,\tfrac12)$, so the first MRRW bound is not the best bound a qubit-output channel can give.
--
--   **Formalization Note** $R_2$ is the base mission's published `PrettyGoodCriterion.rateFunction`. $R_{\mathrm{MQC}}$ is the published `HoneycombCodes.RMQC`, written in the paper's second form of (38), $\min_{1-2\delta\le u\le1}\big[s(u^2)-s\big(u(u-(1-2\delta))\big)\big]$, which is the first form under $u=1-2r$; there `g` is $s$ and the minimum is a real `sInf` (attained). $R_{\mathrm{MRRW}}$ is the published `HoneycombCodes.M1`, with `H2` the base-2 binary entropy $h$.
--
--   Differences from the source:
--   - encoding: $R_{\mathrm{MQC}}(\delta)=\min_{0\le r\le\delta}[s((1-2r)^2)-s(2(\delta-r)(1-2r))]$ → `HoneycombCodes.RMQC`, the real `sInf` of $s(u^2)-s(u(u-(1-2\delta)))$ over $u\in[1-2\delta,1]$; reason: this is the second line of the paper's own (38); $u=1-2r$ maps $[0,\delta]$ onto $[1-2\delta,1]$ with $u(u-(1-2\delta))=2(\delta-r)(1-2r)$, so the two images coincide (checked in Lean), and the continuous objective attains its infimum on the compact interval.
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Theorem 2, p.4 (PDF 6); proof p.37 (PDF 39) via Corollary 23 (p.32) and Proposition 25

import Mathlib
import Definitions.Def_PrettyGoodCriterion_rateFunction
import Definitions.Def_HoneycombCodes_RMQC
import Definitions.Def_HoneycombCodes_M2

set_option autoImplicit false

namespace PrettyGoodCriterion.Supplement

/-- **Theorem 2 (MQC improvement over the first MRRW bound)**, Alrabiah–Guruswami, *Binary code
rate bounds via classical–quantum channels*, arXiv:2608.09347 (held version), p.4 (PDF 6); proof
p.37 (PDF 39) via Corollary 23 and Proposition 25.

For every `δ ∈ (0, 1/2)`, `R₂(δ) ⩽ R_MQC(δ) < R_MRRW(δ)`, where
`R_MQC(δ) = min_{0⩽r⩽δ} [ s((1 − 2r)²) − s(2(δ − r)(1 − 2r)) ]`, `s(D) = h((1 − √(1 − D))/2)` and
`R_MRRW(δ) = h(1/2 − √(δ(1 − δ)))` (Corollary 21).

**Formalization Note.** `R₂` is the base mission's `PrettyGoodCriterion.rateFunction` (equation (1)).
`R_MQC` is the published `HoneycombCodes.RMQC`, the second line of the paper's (38),
`min_{1−2δ⩽u⩽1} [ s(u²) − s(u(u − (1 − 2δ))) ]`, which is the first line under `u = 1 − 2r` (a bijection
of `[0, δ]` onto `[1 − 2δ, 1]`); its `g` is `s` and its minimum an attained real `sInf`. `R_MRRW` is the
published `HoneycombCodes.M1` (`H2` is the base-2 binary entropy `h`). Both conclusions are stated, the
second strict. -/
theorem theorem_2 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    PrettyGoodCriterion.rateFunction δ ≤ HoneycombCodes.RMQC δ ∧
      HoneycombCodes.RMQC δ < HoneycombCodes.M1 δ := by sorry

end PrettyGoodCriterion.Supplement
