-- Prove2me | Theorems.Thm_ValiantModel_theorem_4_5
-- name    : ValiantModel.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:40:30.220028+00:00
-- url     : https://prove2.me/theorems/c1c13e40-a43b-48fd-a364-4047c0467107
-- title:
--   Theorem 4.5, p.20 — uniform success over all potential targets
-- statement:
--   Let $L$ be a learner with sample/query complexity $m$. Then $H$ admits a learner satisfying Definition 12 with sample/query complexity
--
--   $$
--   m_{\mathrm{unif}}(d,\varepsilon,\delta)=m\Bigl(d,\varepsilon,\frac{\delta}{|H_d|}\Bigr).
--   $$
--
--   Thus the guarantee for the true target can be upgraded, at the price of the confidence parameter $\delta/|H_d|$, to a guarantee for every hypothesis consistent with the realized sample and transcript. This is what makes a single transcript certify the whole version space in Theorem 4.7.
--
--   **Formalization Note** $|H_d|$ is `Set.ncard`, the true cardinality on the finite set of Boolean functions. When $H_d=\emptyset$, Lean's $\delta/0=0$ makes the argument $0$, and there is no target to serve.
--
--   Differences from the source:
--   - generalization: H learnable, with mW the complexity of a witnessing learner, polynomial → any learner `L` with any complexity function (`HasComplexity`), no polynomial bound; reason: the argument does not use the polynomial bound; `Learnable` supplies such an `L` and `m`, so the printed statement is the special case
--   - reading: D_h can be any fixed distribution supported on supp(h) → the conclusion holds for every family (ν_h) with ν_h compatible with h, and the learner does not depend on the family; reason: the universal is the stronger reading, and the proof treats an arbitrary fixed D_h
--   - encoding: |Hd| (and δ/|Hd|, undefined in the print when Hd = ∅) → `Set.ncard (H d)`, with Lean's δ / 0 = 0 at H d = ∅; reason: ncard is the true cardinality of the finite set Hd; at H d = ∅ there is no target, so the guarantee is vacuous and the budget m(d, ε, 0) is met by a learner making no call
--   - encoding: a randomized learner with internal randomness → a `PMF` over deterministic protocols on each input (`Learner`); reason: fixing the internal randomness gives a deterministic protocol (p.15), and with a bounded budget on a finite domain only finitely many protocols are distinct; no learner is lost
--   - encoding: at most m(d, ε, δ) positive examples and membership queries → at most m(d, ε, δ) calls on each oracle, on every path of every protocol in the support (`WithinBudget`); reason: this is the paper's own count (Remark 3.1, p.15; proof of Theorem 4.10, p.28)
--   - encoding: d ∈ N, with the sequence starting at H₁ → `1 ≤ d`; reason: the sequence is indexed from 1; `H 0` is not part of the source
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.20 (PDF p.22), Theorem 4.5; Definition 12, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_ValiantModel_HasUniformSuccess

namespace ValiantModel

/-- **Theorem 4.5 (Uniform Success Over All Potential Targets)**, arXiv:2605.13840 (version held),
p.20 (PDF p.22). A learner with complexity `m` yields a learner satisfying Definition 12 with
complexity `munif(d, ε, δ) = m(d, ε, δ / |Hd|)`.

**Formalization Note.** `|Hd|` is `Set.ncard (H d)`, the true cardinality since the set of Boolean
functions on `{0,1}^d` is finite. For `H d = ∅`, Lean's `δ / 0 = 0` makes the argument `0`, and there
is no target to serve, so the statement has no content at that `d`. `m` is any complexity function. -/
theorem theorem_4_5 (H : ConceptSequence) (L : Learner) (m : ℕ → ℝ → ℝ → ℕ)
    (hL : HasComplexity H L m) :
    ∃ L' : Learner, HasUniformSuccess H L' fun d ε δ => m d ε (δ / ((H d).ncard : ℝ)) := by sorry

end ValiantModel
