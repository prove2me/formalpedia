-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_theorem_25
-- name    : UniversalNonstochastic.Main.Supplement.theorem_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:36:29.853607+00:00
-- url     : https://prove2.me/theorems/844710fe-2657-4342-a61f-40a65023d1ea
-- title:
--   Theorem 25 — Kolmogorov's count $N(k,\alpha,\beta)=2^{k-\alpha+O(\log(k+1))}$
-- statement:
--   Let $N(k,\alpha,\beta)$ be the number of objects $\omega$ with $C(\omega)\le k$ that are not $(\alpha,\beta)$-stochastic in Kolmogorov's sense (no finite $\Omega\ni\omega$ with $C(\Omega)\le\alpha$ and $C(\omega)\ge\log|\Omega|-\beta$). There is a constant $c>0$ such that for all $k\in\mathbb N$, $\alpha\in\mathbb N_0$ and $\beta\in[0,\infty]$,
--   $$N(k,\alpha,\beta)\le2^{k-\alpha+c\log(k+1)},\qquad(54)$$
--   and, provided $\alpha+c\le k$,
--   $$N(k,\alpha,\beta)\ge2^{k-\alpha-K(\alpha)-c}.\qquad(55)$$
--   In particular, uniformly in $\beta\in[0,\infty]$ whenever $\alpha+c\le k$,
--   $$N(k,\alpha,\beta)=2^{k-\alpha+O(\log(k+1))};\qquad(56)$$
--   that is, there is a constant $C>0$ with $2^{k-\alpha-C\log(k+1)}\le N(k,\alpha,\beta)\le2^{k-\alpha+C\log(k+1)}$ for all such $k,\alpha,\beta$.
--
--   The fraction of nonstochastic objects among the objects of complexity at most $k$ is about $2^{-\alpha}$; this answers Kolmogorov's 1981 questions.
--
--   Differences from the source:
--   - encoding: N(k, α, β) a cardinality → the cardinality in ℕ ∪ {∞} of D_k ∖ S_{α,β}, compared in ℝ≥0∞; reason: D_k is finite; the upper bound (54) also asserts this, and no ncard default is used
--   - encoding: N(k, α, β) = 2^(k−α+O(log(k+1))) uniformly in β whenever α + c ≤ k → ∃ C > 0 with two-sided bounds 2^(k−α∓C log₂(k+1)) for all k ≥ 1, α, β ∈ [0, ∞] with α + c ≤ k; reason: the O-term is uniform in k, α, β, as the last line of the proof on p.30 provides
--   - encoding: K(α) as a real exponent → ∃ κ : ℕ, K(α) = κ, and the bound with κ; reason: K(α) is valued in ℕ ∪ {∞} in Lean; for an optimal decoder it is finite, and asserting the witness avoids any default value of a conversion at ∞
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Theorem 25, eqs. (54)–(56), p.29 (PDF p.29); N(k, α, β) defined on p.28, proof pp.29–30

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities
import Definitions.Def_UniversalNonstochastic_Main_Supplement_KolmogorovCount

open scoped ENNReal

namespace UniversalNonstochastic.Main.Supplement

/-- Theorem 25, p.29: there is `c > 0` such that for all `k ∈ ℕ`, `α ∈ ℕ₀` and `β ∈ [0, ∞]`,
(54) `N(k, α, β) ≤ 2^{k-α+c log₂(k+1)}` and, provided `α + c ≤ k`,
(55) `N(k, α, β) ≥ 2^{k-α-K(α)-c}` (with `K(α)` a natural number `κ`). In particular (56),
`N(k, α, β) = 2^{k-α+O(log(k+1))}` uniformly in `β ∈ [0, ∞]` whenever `α + c ≤ k`: there is
`C > 0` with `2^{k-α-C log₂(k+1)} ≤ N(k, α, β) ≤ 2^{k-α+C log₂(k+1)}` there.
`N(k, α, β)` is an extended natural (`⊤` for an infinite set), compared in `ℝ≥0∞`. -/
theorem theorem_25 (V : OptimalPlainDecoder) (U : OptimalPrefixDecoder) :
    ∃ c : ℝ, 0 < c ∧
      (∀ (k : ℕ), 1 ≤ k → ∀ (α : ℕ) (β : EReal), 0 ≤ β →
        -- (54)
        ((kolmogorovCount V k α β : ℝ≥0∞) ≤
            ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) - α + c * Real.logb 2 ((k : ℝ) + 1)))) ∧
        -- (55)
        ((α : ℝ) + c ≤ k → ∃ κ : ℕ, KNat U α = κ ∧
            ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) - α - κ - c)) ≤
              (kolmogorovCount V k α β : ℝ≥0∞))) ∧
      -- (56)
      ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (α : ℕ) (β : EReal), 0 ≤ β → (α : ℝ) + c ≤ k →
        ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) - α - C * Real.logb 2 ((k : ℝ) + 1))) ≤
            (kolmogorovCount V k α β : ℝ≥0∞) ∧
          (kolmogorovCount V k α β : ℝ≥0∞) ≤
            ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) - α + C * Real.logb 2 ((k : ℝ) + 1))) := by sorry

end UniversalNonstochastic.Main.Supplement
