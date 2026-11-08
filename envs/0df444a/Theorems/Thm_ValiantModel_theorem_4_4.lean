-- Prove2me | Theorems.Thm_ValiantModel_theorem_4_4
-- name    : ValiantModel.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:21.03204+00:00
-- url     : https://prove2.me/theorems/b6bc9dee-bc71-46ba-94cb-7a66257e8f3e
-- title:
--   Theorem 4.4, p.18 — boosting for Valiant's model
-- statement:
--   Let $L$ be a learner with sample/query complexity $m_W$. For every $\varepsilon\in(0,1)$ and $\delta\in(0,1/2]$ there is a learner satisfying the Valiant guarantee with sample/query complexity
--
--   $$
--   m(d,\varepsilon,\delta)=m_W\Bigl(d,\frac1{18},\frac13\Bigr)\cdot O\Bigl(\frac1\varepsilon\log_2\frac1\delta\Bigr).
--   $$
--
--   A learner at the fixed parameters $(1/18,1/3)$ therefore determines the complexity for all parameters, with linear dependence on $1/\varepsilon$ and logarithmic dependence on $1/\delta$. The value $m_W(d,1/18,1/3)=0$ is included.
--
--   Differences from the source:
--   - generalization: H learnable, with mW the complexity of a witnessing learner, polynomial → any learner `L` with any complexity function (`HasComplexity`), no polynomial bound; reason: the argument does not use the polynomial bound; `Learnable` supplies such an `L` and `m`, so the printed statement is the special case
--   - encoding: O(·) → an absolute constant `C > 0`, quantified before the class, the learner and d; reason: the standard meaning of O(·); it depends on nothing
--   - encoding: a randomized learner with internal randomness → a `PMF` over deterministic protocols on each input (`Learner`); reason: fixing the internal randomness gives a deterministic protocol (p.15), and with a bounded budget on a finite domain only finitely many protocols are distinct; no learner is lost
--   - encoding: at most m(d, ε, δ) positive examples and membership queries → at most m(d, ε, δ) calls on each oracle, on every path of every protocol in the support (`WithinBudget`); reason: this is the paper's own count (Remark 3.1, p.15; proof of Theorem 4.10, p.28)
--   - encoding: d ∈ N, with the sequence starting at H₁ → `1 ≤ d`; reason: the sequence is indexed from 1; `H 0` is not part of the source
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.18 (PDF p.20), Theorem 4.4; proof pp.56–59 (PDF pp.58–61)

import Mathlib
import Definitions.Def_ValiantModel_Learnable

namespace ValiantModel

/-- **Theorem 4.4 (Boosting for Valiant's Model)**, arXiv:2605.13840 (version held), p.18 (PDF p.20);
proof pp.56–59 (PDF pp.58–61). For every `ε ∈ (0,1)` and `δ ∈ (0, 1/2]` there is a learner with the
Valiant guarantee and complexity `mW(d, 1/18, 1/3) · O((1/ε) log (1/δ))`.

**Formalization Note.** `O(·)` is an absolute constant `C` quantified before the class and the
learner; `mW` is any complexity function, and `mW(d, 1/18, 1/3) = 0` is not excluded. Logarithms are
base two (§3, p.14, PDF p.16). -/
theorem theorem_4_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ConceptSequence) (L : Learner) (mW : ℕ → ℝ → ℝ → ℕ),
      HasComplexity H L mW →
      ∃ L' : Learner,
        ∀ d : ℕ, 1 ≤ d → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ ≤ 1 / 2 →
          WithinBudget (L' d ε δ)
              ((mW d (1 / 18) (1 / 3) : ℝ) * (C * ((1 / ε) * Real.logb 2 (1 / δ)))) ∧
            Guarantee (H d) (L' d ε δ) ε δ := by sorry

end ValiantModel
