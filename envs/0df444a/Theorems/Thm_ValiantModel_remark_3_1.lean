-- Prove2me | Theorems.Thm_ValiantModel_remark_3_1
-- name    : ValiantModel.remark_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:01.620765+00:00
-- url     : https://prove2.me/theorems/dbc0370c-ae96-4c73-aed2-6c1bda6c602c
-- title:
--   Remark 3.1, p.15 — positive examples may be collected first
-- statement:
--   Let $L$ be a learner with sample/query complexity $m$. Then there is a learner $L'$ with the same complexity such that, on every input $(d,\varepsilon,\delta)$ with $d\ge 1$ and $\varepsilon,\delta\in(0,1)$, every deterministic protocol in the support of $L'$ first makes exactly $m(d,\varepsilon,\delta)$ example calls and from then on only queries, at most $m(d,\varepsilon,\delta)$ of them. Moreover, for every hypothesis $h$ and every distribution $D$, the output of $L'$ on the oracles for $h$ and $D$ has the same law as the output of $L$.
--
--   So a learner may be assumed to observe its whole positive sample first and then, with its internal randomness fixed, to run a deterministic adaptive query strategy. The results below build on this normal form.
--
--   Differences from the source:
--   - generalization: H learnable, with mW the complexity of a witnessing learner, polynomial → any learner `L` with any complexity function (`HasComplexity`), no polynomial bound; reason: the argument does not use the polynomial bound; `Learnable` supplies such an `L` and `m`, so the printed statement is the special case
--   - generalization: without changing its guarantee → the same guarantee, and also the same law of the output for every h and D; reason: the simulation preserves the law; the guarantee is a function of it
--   - encoding: a randomized learner with internal randomness → a `PMF` over deterministic protocols on each input (`Learner`); reason: fixing the internal randomness gives a deterministic protocol (p.15), and with a bounded budget on a finite domain only finitely many protocols are distinct; no learner is lost
--   - encoding: at most m(d, ε, δ) positive examples and membership queries → at most m(d, ε, δ) calls on each oracle, on every path of every protocol in the support (`WithinBudget`); reason: this is the paper's own count (Remark 3.1, p.15; proof of Theorem 4.10, p.28)
--   - encoding: d ∈ N, with the sequence starting at H₁ → `1 ≤ d`; reason: the sequence is indexed from 1; `H 0` is not part of the source
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.15 (PDF p.17), Remark 3.1

import Mathlib
import Definitions.Def_ValiantModel_Learnable
import Definitions.Def_ValiantModel_ProtocolShape

namespace ValiantModel

/-- **Remark 3.1 (Positive Examples May Be Collected First)**, arXiv:2605.13840 (version held), p.15
(PDF p.17). Any learner with complexity `m` can be replaced by a learner that on `(d, ε, δ)` first
draws exactly `m(d, ε, δ)` examples and then only queries, at most `m(d, ε, δ)` times, with the same
guarantee and, for every target and distribution, the same law of the output.

**Formalization Note.** For any complexity function `m`, not only a polynomial one. The same law of
the output is stronger than the printed "without changing its guarantee". -/
theorem remark_3_1 (H : ConceptSequence) (L : Learner) (m : ℕ → ℝ → ℝ → ℕ)
    (hL : HasComplexity H L m) :
    ∃ L' : Learner, HasComplexity H L' m ∧
      ∀ d : ℕ, 1 ≤ d → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        (∀ p ∈ (L' d ε δ).support, Protocol.ExamplesFirst (m d ε δ) p) ∧
        ∀ (h : Hypothesis d) (D : PMF (Point d)),
          (runLaw (L' d ε δ) h D).map Outcome.output = (runLaw (L d ε δ) h D).map Outcome.output := by sorry

end ValiantModel
