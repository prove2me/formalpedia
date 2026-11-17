-- Prove2me | Theorems.Thm_PhysReaudit_Supplement_theorem_6
-- name    : PhysReaudit.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:25:42.772652+00:00
-- url     : https://prove2.me/theorems/267085d6-597c-4389-9e63-9de6f83e6a38
-- title:
--   Theorem 6 — uniform reuse from a fixed target budget: one batch of $n\ge2(\kappa_{\max}p/\varepsilon)^2\log(2/\delta)$ target observations certifies every $\pi_\kappa$, at cost $\mu(a,d)n$
-- statement:
--   Fix a corridor of depth $d\ge0$ with survival probability $a\in(0,1]$ and reach probability $p=a^d$, an unknown target parameter $q\in[0,1]$, and the declared policy family $\Pi=\{\pi_\kappa:0\le\kappa\le\kappa_{\max}\}$ with $0<\kappa_{\max}\le1$ and advantage $\Delta_q(\pi_\kappa)=b-\kappa pq$. The old transcript and any private randomness have a law that does not depend on $q$. Let $0<\delta<1/2$ and $0<\varepsilon<b<\kappa_{\max}p$, and let $n$ be a natural number with
--   $$
--   n\ \ge\ 2\Big(\frac{\kappa_{\max}p}{\varepsilon}\Big)^2\log\frac2\delta
--   $$
--   (for instance the printed $n=\lceil 2(\kappa_{\max}p/\varepsilon)^2\log(2/\delta)\rceil$). Collect $n$ target observations through full root-started episodes, let $\hat q$ be their mean, and put
--   $$
--   r=\sqrt{\frac{\log(2/\delta)}{2n}},\qquad U=\min\{1,\hat q+r\},\qquad L(\kappa)=b-\kappa pU .
--   $$
--   Accept $\pi_\kappa$ precisely when $L(\kappa)\ge0$. Then, for every $q\in[0,1]$:
--
--   1. there is a single event of probability at least $1-\delta$ on which, for every $\kappa\in[0,\kappa_{\max}]$, acceptance implies safety ($L(\kappa)\ge0\Rightarrow\Delta_q(\pi_\kappa)\ge0$) and every policy with advantage at least $\varepsilon$ is accepted ($\Delta_q(\pi_\kappa)\ge\varepsilon\Rightarrow L(\kappa)\ge0$);
--   2. the expected fresh physical cost is exactly $\mu(a,d)\,n$, where $\mu(a,d)=(1+\sum_{j=0}^d a^j)/a^d$.
--
--   One fixed batch of target observations certifies the whole declared family at once, at a cost that does not depend on $q$. The quantifier over $\kappa$ sits inside the probability, which is stronger than testing one candidate at a time.
--
--   **Formalization Note** The access model, the law $P_q$, the cost and $\Delta_q$ are the published definitions of the base mission; the audit is the published full-traversal rule halting after $n$ target outcomes.
--
--   Differences from the source:
--
--   - generalization: take exactly n = ⌈2(κmax p/ε)² log(2/δ)⌉ target observations → every n ∈ ℕ with 2(κmax p/ε)² log(2/δ) ≤ n; reason: the printed ceiling is one such n, so the statement specializes to the source's; r is computed from the chosen n
--   - encoding: q ∈ [0, 1] unknown; navigation and target outcomes with their stated laws; old-transcript laws common under the alternatives → side variable w ∼ ν (law free of q) independent of an i.i.d. Bernoulli(a) navigation tape and an i.i.d. Bernoulli(q) target tape (the published lawQ); the statement holds for every q ∈ [0, 1]; reason: the published base model; the same joint law of old data and fresh history
--   - encoding: take n target observations through full root-started episodes; target mean q̂ → budgetRule W n = the published fullTraversalRule halting once n target outcomes are recorded; q̂ = (successes among the outcomes recorded when it halts)/n (empty list, q̂ = 0, on the null set of never-halting paths); reason: the same audit and the same q̂ on every path where the audit halts, which has probability one when a > 0
--   - encoding: policies π_κ, 0 ≤ κ ≤ κmax, with Δ_q(π_κ) = b − κpq; "accepted policy is safe" → κ ∈ Set.Icc 0 κmax; Δ_q(π_κ) = Delta a d b κ q (published); safe = 0 ≤ Delta; reason: the source identifies π_κ with κ; safety is nonnegative advantage, as in the source's proof
--   - encoding: simultaneously sound and ε-complete for all κ: one event of probability at least 1 − δ on which every accepted policy is safe and every policy with advantage at least ε is accepted → ∃ measurable E with lawQ ν a q E ≥ 1 − δ such that for all ω ∈ E and all κ ∈ [0, κmax]: (0 ≤ L(κ) → 0 ≤ Δ_q(π_κ)) ∧ (ε ≤ Δ_q(π_κ) → 0 ≤ L(κ)); reason: the source's definition of the family guarantee (§5, p.5), with ∀κ inside the event
--   - encoding: expected fresh physical cost µ(a, d)n → expCost (budgetRule W n) ν a d q = ENNReal.ofReal (mu a d * n), costs counted in ℕ∞ and expectations in ℝ≥0∞ (published expCost); reason: the published cost convention; the value µ(a, d)n is finite
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), Theorem 6 (Uniform reuse from a fixed target budget), p.5 (PDF p.6); the family guarantee as defined in §5, p.5 (PDF p.6): "We require one event of probability at least 1 − δ on which every accepted policy is safe and every policy with advantage at least ε is accepted."

import Mathlib
import Definitions.Def_PhysReaudit_mu
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_Rule
import Definitions.Def_PhysReaudit_run
import Definitions.Def_PhysReaudit_lawQ
import Definitions.Def_PhysReaudit_fullTraversalRule
import Definitions.Def_PhysReaudit_Supplement_certL

open MeasureTheory

namespace PhysReaudit.Supplement

open PhysReaudit

/-- **Theorem 6 (Uniform reuse from a fixed target budget)** (Q. Li, *When Can Physical Evidence Survive a
World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), Theorem 6, p.5 (PDF p.6)).

Fix depth `d`, survival `a ∈ (0, 1]`, `p = a^d`, `0 < κmax ≤ 1`, `0 < δ < 1/2`, `0 < ε < b < κmax p`, a side
law `ν` and a number of target observations `n ∈ ℕ` with `n ≥ 2(κmax p/ε)² log(2/δ)`. Run `budgetRule W n`
(full root-started episodes until `n` target outcomes are recorded) and let `L(κ) = b − κpU`,
`U = min{1, q̂ + r}`, `r = √(log(2/δ)/(2n))` (`certL`). Then for every `q ∈ [0, 1]`:
1. there is one event of probability at least `1 − δ` on which, for every `κ ∈ [0, κmax]`, `L(κ) ≥ 0`
   implies `Δ_q(π_κ) ≥ 0` (soundness) and `Δ_q(π_κ) ≥ ε` implies `L(κ) ≥ 0` (ε-completeness);
2. the expected physical cost is exactly `µ(a, d) n`.

**Formalization Note** The theorem is stated for every natural `n` at least the printed value; the printed
`n = ⌈2(κmax p/ε)² log(2/δ)⌉` is one of them. -/
theorem theorem_6 {W : Type} [MeasurableSpace W] (ν : Measure W) [IsProbabilityMeasure ν]
    {a b κmax ε δ : ℝ} {d n : ℕ} (ha : 0 < a) (ha1 : a ≤ 1) (hκ : 0 < κmax) (hκ1 : κmax ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 2) (hε : 0 < ε) (hεb : ε < b) (hb : b < κmax * a ^ d)
    (hn : 2 * (κmax * a ^ d / ε) ^ 2 * Real.log (2 / δ) ≤ n) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (∃ E : Set (Omega W), MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ lawQ ν a q E ∧
      ∀ ω ∈ E, ∀ κ ∈ Set.Icc (0 : ℝ) κmax,
        (0 ≤ certL a d n b δ κ ω → 0 ≤ Delta a d b κ q) ∧
        (ε ≤ Delta a d b κ q → 0 ≤ certL a d n b δ κ ω)) ∧
    expCost (budgetRule W n) ν a d q = ENNReal.ofReal (mu a d * n) := by sorry

end PhysReaudit.Supplement
