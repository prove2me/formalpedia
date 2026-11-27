-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_lemma_A_15
-- name    : SampleMechDesign.Supplement.lemma_A_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:52:01.469724+00:00
-- url     : https://prove2.me/theorems/6c2c63b0-c320-4f0c-871e-aa1d3aa437cd
-- title:
--   Lemma A.15 (corrected: the value at the tie point $\gamma^*$ belongs to either side) — the $\gamma$-MBA profit rises, then falls
-- statement:
--   For a valuation vector $v$, let $\mathrm{profit}_v(\gamma)$ be the profit of the γ-MBA on $v$, as a function of $\gamma$. There is $\gamma^*\in[0,\infty)$ such that either
--
--   1. $\mathrm{profit}_v$ is non-decreasing on $[0,\gamma^*]$ and non-increasing on $(\gamma^*,\infty)$, or
--   2. $\mathrm{profit}_v$ is non-decreasing on $[0,\gamma^*)$ and non-increasing on $[\gamma^*,\infty)$.
--
--   This holds for every cost function, every valuation vector and every tie-breaking rule. At $\gamma^*$ the auction switches to a grand-bundle allocation and the profit drops by the lost boost, so the value at $\gamma^*$ is the left limit or the right value according to how the tie at $\gamma^*$ is broken.
--
--   The paper states alternative 1 only, which fails for tie-breaking rules that prefer the grand bundle at $\gamma^*$. With zero cost, $n=m=2$, buyer 1 valuing every bundle containing item 1 at $2$, buyer 2 valuing every bundle containing item 2 at $2$, and all other bundles at $0$, one gets $\mathrm{profit}_v(\gamma)=2\gamma$ on $[0,2)$ and $\mathrm{profit}_v(\gamma)=2$ on $[2,\infty)$ under that rule, and no $\gamma^*$ satisfies alternative 1.
--
--   The lemma is the structural fact behind the upper bound $\mathrm{Pdim}\le2$ of Theorem A.14: every superlevel set $\{\gamma:\mathrm{profit}_v(\gamma)>z\}$ is an interval.
--
--   Differences from the source:
--   - correction: ∃ γ* ∈ [0, ∞): non-decreasing on [0, γ*] and non-increasing on (γ*, ∞) → ∃ γ* ≥ 0 with that, or non-decreasing on [0, γ*) and non-increasing on [γ*, ∞); reason: false as printed for tie-breaking rules preferring the grand bundle at γ*: zero cost, n = m = 2, v₁(q) = 2·[1 ∈ q], v₂(q) = 2·[2 ∈ q] gives profit 2γ on [0, 2) and 2 on [2, ∞)
--   - reading: the tie-breaking rule is not specified and the cost function is general → every tie-breaking rule (depending on v and the set of maximizers) and every cost function; reason: the paper leaves ties open; the corrected statement holds for all of them
--   - reading: Q^{−i}: the allocation without buyer i's participation → the maximum over the allocations giving buyer i nothing; reason: as in the proof of Lemma A.15 (p.33, "excluding buyer i")
--   - reading: the profit of the γ-MBA → total payment minus the cost of the allocation; reason: the paper's notion of profit (lotteries, p.14); the proof's profit Σ payments agrees with it at zero cost, and the corrected statement holds for both
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Lemma A.15, p.32 (PDF p.32); proof pp.33–34; Appendix A.2, p.31

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_mbaProfit

namespace SampleMechDesign.Supplement

/-- **Lemma A.15, corrected at the tie point.** Balcan, Sandholm, Vitercik,
arXiv:1705.00243v6, p.32 (proof pp.33–34). For a valuation vector `v`, let `profit_v(γ)` be the
profit of the `γ`-MBA on `v`. There is `γ* ∈ [0, ∞)` such that either `profit_v` is
non-decreasing on `[0, γ*]` and non-increasing on `(γ*, ∞)`, or it is non-decreasing on
`[0, γ*)` and non-increasing on `[γ*, ∞)`.

**Formalization Note.** Correction: the paper asserts the first alternative only, and it fails
for tie-breaking rules that pick a grand-bundle allocation at the tie point `γ*`. Counterexample
(zero cost, `n = m = 2`): buyer 1 values every bundle containing item 1 at `2`, buyer 2 every
bundle containing item 2 at `2`, all other bundles `0`; ties broken towards allocations giving the
grand bundle to a buyer. Then `profit_v(γ) = 2γ` on `[0, 2)` and `profit_v(γ) = 2` on `[2, ∞)`,
which is non-decreasing on `[0, 2)` and non-increasing on `[2, ∞)`, but has no `γ*` of the
printed kind. At `γ*` the profit jumps down by `γ*` (the boost is lost), so the value at `γ*` is
the left limit or the right value according to the tie-break; the two alternatives cover both.
The statement holds for every cost function `c`, every valuation vector and every tie-breaking
rule `tb`. -/
theorem lemma_A_15 {n m : ℕ} (c : Bundles n m → ℝ)
    (tb : BVal n m → Finset (Alloc n m) → Alloc n m) (htb : IsChoice tb) (v : BVal n m) :
    ∃ γs : ℝ, 0 ≤ γs ∧
      ((MonotoneOn (fun γ => mbaProfit c tb γ v) (Set.Icc 0 γs) ∧
          AntitoneOn (fun γ => mbaProfit c tb γ v) (Set.Ioi γs)) ∨
        (MonotoneOn (fun γ => mbaProfit c tb γ v) (Set.Ico 0 γs) ∧
          AntitoneOn (fun γ => mbaProfit c tb γ v) (Set.Ici γs))) := by sorry

end SampleMechDesign.Supplement
