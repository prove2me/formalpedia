-- Prove2me | Theorems.Thm_ValiantModel_theorem_4_9
-- name    : ValiantModel.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:32.588203+00:00
-- url     : https://prove2.me/theorems/faf69948-4d23-4bbd-abde-44a9747a5fc0
-- title:
--   Theorem 4.9, p.26 — query-based compression implies learnability
-- statement:
--   Suppose that for each $d\ge 1$ the class $H_d$ has a nondecreasing query-based compression rate $\kappa_d:\mathbb N\to\mathbb N$ (Definition 15). Then there is a learner, given $n$ as input, with the following guarantee. For all $\varepsilon,\delta\in(0,1)$, every target $h^\star\in H_d$, every distribution $D$ compatible with $h^\star$ and every $n$ with
--
--   $$
--   n\ge c\cdot\frac{(d+1)(\kappa_d(n)+1)+\log_2(1/\delta)}{\varepsilon},
--   $$
--
--   the learner makes exactly $n$ example calls and at most $\kappa_d(n)$ membership queries, and with probability at least $1-\delta$ outputs a hypothesis satisfying Definition 1. Here $c>0$ is absolute. In particular $m(d,\varepsilon,\delta)=n+\kappa_d(n)$ is a valid complexity bound.
--
--   Moreover, if $\kappa_d(n)=q_d\,(1+\lceil\log_{3/2}n\rceil)$, there is a learner with complexity
--
--   $$
--   m(d,\varepsilon,\delta)=O\bigl(A\log_2\max(A,1)\bigr),\qquad A=\frac{d\,q_d+\log_2(1/\delta)}{\varepsilon}.
--   $$
--
--   This is the direction from compression to learnability in Theorem 1.1. Note that $n$ appears on both sides of its condition, as printed.
--
--   Differences from the source:
--   - reading: O(((d q_d + log 1/δ)/ε) · log((d q_d + log 1/δ)/ε)) → `C · A · log₂(max A 1)` with `A = (d q_d + log₂(1/δ))/ε`; reason: for A ≥ 1 this is the printed expression. A < 1 forces q_d = 0, and there the printed expression is negative, which no budget can meet: for Hd = {h}, q_d = 0, ε = δ = 0.9 we have A < 1. There the learner makes no call, so the clipped bound 0 holds
--   - encoding: the learner uses n, which it must be told → the learner takes n as input and does not otherwise use ε, δ, which is how the proof's learner works; reason: the theorem quantifies over n satisfying a condition that involves ε, δ and n itself
--   - encoding: Ω(·) and O(·) → absolute constants `c, C > 0`, quantified before the class and the rates; reason: the standard meaning; they depend on nothing
--   - encoding: a randomized learner with internal randomness → a `PMF` over deterministic protocols on each input (`Learner`); reason: fixing the internal randomness gives a deterministic protocol (p.15), and with a bounded budget on a finite domain only finitely many protocols are distinct; no learner is lost
--   - encoding: d ∈ N, with the sequence starting at H₁ → `1 ≤ d`; reason: the sequence is indexed from 1; `H 0` is not part of the source
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.26 (PDF p.28), Theorem 4.9; p.28 (PDF p.30), the last display of its proof

import Mathlib
import Definitions.Def_ValiantModel_Learnable
import Definitions.Def_ValiantModel_ProtocolShape
import Definitions.Def_ValiantModel_IsCompressionRate

namespace ValiantModel

/-- **Theorem 4.9 (Query-Based Compression Implies Learnability)**, arXiv:2605.13840 (version held),
p.26 (PDF p.28). Nondecreasing compression rates `κ_d` give a learner that takes `n` as input, makes
exactly `n` example calls and at most `κ_d(n)` queries, so `n + κ_d(n)` is a valid complexity, and
meets the Valiant guarantee at `(ε, δ)` whenever `n ≥ c ((d+1)(κ_d(n)+1) + log(1/δ)) / ε`. For
`κ_d(n) = q_d (1 + ⌈log_{3/2} n⌉)` there is a learner with complexity `O(A · log A)`, where
`A = (d q_d + log(1/δ)) / ε`, with the logarithm read as `log (max A 1)`.

**Formalization Note.** `Ω(·)` and `O(·)` are absolute constants `c`, `C`, quantified before the
class. `n` appears on both sides of its condition, as printed; the learner does not otherwise use
`ε, δ`. The print's last clause has `log A` where this has `log (max A 1)`; they agree for
`A ≥ 1`. `A < 1` forces `q_d = 0`, and there `log A < 0` would make the printed bound negative, while
this bound is `0`. Logarithms are
base two (§3, p.14, PDF p.16). `Real.logb` at `n = 0` is `0` by Lean's convention, which gives
`κ_d(0) = q_d`; `n = 0` never meets the condition. -/
theorem theorem_4_9 :
    (∃ c : ℝ, 0 < c ∧ ∀ (H : ConceptSequence) (κ : ℕ → ℕ → ℕ),
      (∀ d : ℕ, 1 ≤ d → Monotone (κ d)) →
      (∀ d : ℕ, 1 ≤ d → IsCompressionRate (H d) (κ d)) →
      ∃ L : (d : ℕ) → ℕ → PMF (Protocol d),
        ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ,
          (∀ p ∈ (L d n).support, p.ExactExamples n ∧ p.queryDepth ≤ κ d n) ∧
          WithinBudget (L d n) ((n + κ d n : ℕ) : ℝ) ∧
          ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
            c * ((((d : ℝ) + 1) * ((κ d n : ℝ) + 1) + Real.logb 2 (1 / δ)) / ε) ≤ (n : ℝ) →
            Guarantee (H d) (L d n) ε δ) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (H : ConceptSequence) (q : ℕ → ℕ),
      (∀ d : ℕ, 1 ≤ d →
        IsCompressionRate (H d) fun n => q d * (1 + ⌈Real.logb (3 / 2) (n : ℝ)⌉₊)) →
      ∃ L : Learner,
        ∀ d : ℕ, 1 ≤ d → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          WithinBudget (L d ε δ)
              (C * ((((d : ℝ) * (q d : ℝ) + Real.logb 2 (1 / δ)) / ε) *
                Real.logb 2 (max (((d : ℝ) * (q d : ℝ) + Real.logb 2 (1 / δ)) / ε) 1))) ∧
            Guarantee (H d) (L d ε δ) ε δ) := by sorry

end ValiantModel
