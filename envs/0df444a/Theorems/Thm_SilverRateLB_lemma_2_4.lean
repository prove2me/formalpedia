-- Prove2me | Theorems.Thm_SilverRateLB_lemma_2_4
-- name    : SilverRateLB.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:13.050545+00:00
-- url     : https://prove2.me/theorems/93e83d13-d07b-427f-b457-84278d444ae9
-- title:
--   Lemma 2.4 — lower bound (7) for every admissible checkpoint set
-- statement:
--   Fix $\varepsilon,\gamma>0$, let $c=\sqrt{1+2\gamma+\varepsilon^2}$, $R=\sqrt{\varepsilon^2+(1+\gamma)^2}$ and
--   $$a=\max\Bigl\{2,\ \frac2c\Bigl(\varepsilon+\varepsilon^{-1}\Bigl[\frac{c(1+\gamma+R)}{\varepsilon(\gamma+R)}\Bigr]^{R/\gamma}\Bigr)\Bigr\}.$$
--   For every nonnegative schedule $H=(h_1,\dots,h_n)$ and every admissible checkpoint set $T$, with $b_i,s_i$ as in (4),
--   $$\mathscr R_n(H)\ \ge\ \frac{1}{4(1+s_{k+1})}\prod_{i=1}^k\Bigl[\frac{b_i-2}{c(a+s_i)}\Bigr]^2.\tag{7}$$
--
--   This is the hard-function bound for a fixed checkpoint set; the rest of the proof chooses $T$ to make it as large as possible, uniformly in $H$.
--
--   Differences from the source:
--   - encoding: ℛ_n with the paper's convention L = 1 (footnote 6, p. 6) → worstCaseRate 1; reason: the paper works with L = 1 in Sections 2–3 and the proofs; footnote 6 reduces every L to it
--   - encoding: H = (h_1, …, h_n) ∈ [0,∞)^n → H : List ℝ with nonnegative entries, n = H.length; reason: same schedules
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Lemma 2.4, (7), p. 11

import Mathlib
import Definitions.Def_SilverRateLB_aOf
import Definitions.Def_SilverRateLB_gapMass
import Definitions.Def_SilverRateLB_worstCaseRate

namespace SilverRateLB

/-- **Lemma 2.4 (lower bound for a checkpoint set).** Fix `ε, γ > 0`, `c = √(1+2γ+ε²)`,
`R = √(ε²+(1+γ)²)` and `a = max{2, (2/c)(ε + ε⁻¹[c(1+γ+R)/(ε(γ+R))]^{R/γ})}`. For every
nonnegative schedule `H = (h_1, …, h_n)` and admissible checkpoint set `T`,
`ℛ_n(H) ≥ (1/(4(1+s_{k+1}))) ∏_{i=1}^k [(b_i − 2)/(c(a + s_i))]²` (7).

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Lemma 2.4, (7), p. 11.

**Formalization Note** `ℛ_n` is `worstCaseRate 1`: the paper works with `L = 1` in Sections 2–3
and the proofs (footnote 6, p. 6). `b_i`, `s_i` are `ckptStep`, `gapMass` of (4); `k = T.card`. -/
theorem lemma_2_4 (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) (H : List ℝ) (hH : ∀ h ∈ H, 0 ≤ h)
    (T : Finset ℕ) (hT : IsAdmissible H T) :
    ENNReal.ofReal (1 / (4 * (1 + gapMass H T (T.card + 1))) *
        ∏ i ∈ Finset.Icc 1 T.card,
          ((ckptStep H T i - 2) / (cOf ε γ * (aOf ε γ + gapMass H T i))) ^ 2)
      ≤ worstCaseRate 1 H := by sorry

end SilverRateLB
