-- Prove2me | Theorems.Thm_ValiantModel_lemma_B_1
-- name    : ValiantModel.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:39.515199+00:00
-- url     : https://prove2.me/theorems/ecb4930c-d5b1-4ca2-8a29-8507ec8c3713
-- title:
--   Lemma B.1, p.55 — confidence amplification
-- statement:
--   Let $L$ be a learner with sample/query complexity $m_W$, and write $m:=m_W(d,1/18,1/3)$. There is an absolute constant $C>0$ such that for every $d\ge 1$ and every $\eta\in(0,1/2]$ there is a learner $L_\eta$ that, for every target $h^\star\in H_d$ and every distribution $\mu$ compatible with $h^\star$, with probability at least $1-\eta$ outputs a hypothesis satisfying the Valiant conditions with error parameter $1/3$, and makes at most
--
--   $$
--   C\,m\,\log_2\frac1\eta
--   $$
--
--   calls to each oracle.
--
--   This reduces the failure probability from the constant $1/3$ to any $\eta$ at a logarithmic cost, and it is the first step of the boosting theorem.
--
--   Differences from the source:
--   - generalization: H learnable, with mW the complexity of a witnessing learner, polynomial → any learner `L` with any complexity function (`HasComplexity`), no polynomial bound; reason: the argument does not use the polynomial bound; `Learnable` supplies such an `L` and `m`, so the printed statement is the special case
--   - encoding: O(·) → an absolute constant `C > 0`, quantified before the class, the learner and d; reason: the standard meaning of O(·); it depends on nothing
--   - encoding: a randomized learner with internal randomness → a `PMF` over deterministic protocols on each input (`Learner`); reason: fixing the internal randomness gives a deterministic protocol (p.15), and with a bounded budget on a finite domain only finitely many protocols are distinct; no learner is lost
--   - encoding: at most m(d, ε, δ) positive examples and membership queries → at most m(d, ε, δ) calls on each oracle, on every path of every protocol in the support (`WithinBudget`); reason: this is the paper's own count (Remark 3.1, p.15; proof of Theorem 4.10, p.28)
--   - encoding: d ∈ N, with the sequence starting at H₁ → `1 ≤ d`; reason: the sequence is indexed from 1; `H 0` is not part of the source
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.55 (PDF p.57), Lemma B.1 and display (8)

import Mathlib
import Definitions.Def_ValiantModel_Learnable

namespace ValiantModel

/-- **Lemma B.1 (Confidence Amplification)**, arXiv:2605.13840 (version held), p.55 (PDF p.57). With
`m := mW(d, 1/18, 1/3)` (display (8)), for every `η ∈ (0, 1/2]` there is a learner that with
probability at least `1 - η` meets the Valiant conditions with error parameter `1/3`, using
`O(m log 1/η)` example calls and membership queries.

**Formalization Note.** `O(·)` is an absolute constant `C`, quantified before the class and the
learner. Logarithms are base two (§3, p.14, PDF p.16); `1/η ≥ 2`, so the logarithm is at least `1`.
`mW` is any complexity function. -/
theorem lemma_B_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ConceptSequence) (L : Learner) (mW : ℕ → ℝ → ℝ → ℕ),
      HasComplexity H L mW →
      ∃ Lη : (d : ℕ) → ℝ → PMF (Protocol d),
        ∀ d : ℕ, 1 ≤ d → ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
          WithinBudget (Lη d η) (C * (mW d (1 / 18) (1 / 3) : ℝ) * Real.logb 2 (1 / η)) ∧
          Guarantee (H d) (Lη d η) (1 / 3) η := by sorry

end ValiantModel
