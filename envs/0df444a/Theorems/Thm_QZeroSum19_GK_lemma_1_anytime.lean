-- Prove2me | Theorems.Thm_QZeroSum19_GK_lemma_1_anytime
-- name    : QZeroSum19.GK.lemma_1_anytime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:11.836724+00:00
-- url     : https://prove2.me/theorems/8c3572e7-e90f-4c10-a217-bca95e250c97
-- title:
--   Lemma 1, p. 3, first sentence (corrected to 1 − δ) — with η(t) = 1/(2√t), w.p. ≥ 1 − δ all iterates are ε′(t)-optimal
-- statement:
--   Let $n,m\ge1$, $A\in[-1,1]^{n\times m}$ and $\delta\in(0,1/3)$. Run Algorithm 1 with the anytime step $\eta(\tau)=1/(2\sqrt\tau)$. Then, with probability at least $1-\delta$, for every $t\ge1$ the normalized iterates $x_t/\|x_t\|_1$ and $y_t/\|y_t\|_1$ are $\varepsilon'(t)$-optimal strategies for Alice and Bob, where
--   $$\varepsilon'(t)=\frac{2}{\sqrt t}\Big(3\ln t+\ln(nm)+\ln(1/\delta)+2\Big).$$
--
--   This is the anytime guarantee of Lemma 1: the accuracy of the running solutions improves like $\tilde O(1/\sqrt t)$ without the target accuracy being fixed in advance.
--
--   **Formalization Note** The page prints "with probability at least $\delta$"; the proof concludes that the total failure probability is at most $\delta$, so the statement here is "at least $1-\delta$" (a correction of a printed slip). The event "for all $t$" of an infinite run is stated for every finite horizon $t_0$, simultaneously for all $1\le t\le t_0$; since the law of the first $t_0$ draws does not depend on the horizon, this is equivalent to the infinite-run statement by continuity of probability.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 3, Lemma 1, first sentence (proof pp. 4–5); printed 'at least δ' corrected to 1 − δ

import Mathlib
import Definitions.Def_QZeroSum19_GK_Setting

open Matrix

namespace QZeroSum19.GK

/-- **Lemma 1** (p. 3), anytime version, probability corrected from the printed "at least δ" to
`1 − δ`: for `δ ∈ (0, 1/3)`, with steps `η(τ) = 1/(2√τ)`, with probability at least `1 − δ`
the normalized iterates after every `s ≥ 1` iterations are `ε′(s)`-optimal, where
`ε′(s) = (2/√s)(3 ln s + ln(nm) + ln(1/δ) + 2)`. Stated for the first `t₀` iterations, for
every horizon `t₀`. -/
theorem lemma_1_anytime {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (δ : ℝ) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (t₀ : ℕ) :
    1 - δ ≤ prob A etaAnytime t₀ (fun ω => ∀ s : ℕ, 1 ≤ s → s ≤ t₀ →
      IsEpsOptimalAlice A (epsAnytime n m δ s) (normalize (xAfter etaAnytime ω s)) ∧
      IsEpsOptimalBob A (epsAnytime n m δ s) (normalize (yAfter etaAnytime ω s))) := by sorry

end QZeroSum19.GK
