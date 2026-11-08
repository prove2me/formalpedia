-- Prove2me | Theorems.Thm_ValiantModel_theorem_1_1_characterization
-- name    : ValiantModel.theorem_1_1_characterization
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:33.197138+00:00
-- url     : https://prove2.me/theorems/2ef8075c-a139-4bb6-96d6-16d1e9466998
-- title:
--   Theorem 1.1 (Characterization), p.3 — learnability in Valiant's model $\iff$ $\mathrm{poly}(d)$-size adaptive-query compression
-- statement:
--   A sequence of concept classes $H=(H_1,H_2,\dots)$ is learnable in Valiant's model if and only if every realizable positive sample $S\subseteq\{0,1\}^d$ admits an adaptive-query compression scheme of size $\mathrm{poly}(d)$. Explicitly, $H$ is learnable if and only if there are constants $C,k$ such that for every $d\ge 1$ and every $S\subseteq\{0,1\}^d$ with $V(S)\neq\emptyset$ there is a deterministic adaptive query strategy $\Sigma_S$ with
--
--   $$
--   \mathrm{depth}(\Sigma_S)\le C\,d^{\,k},\qquad S\subseteq\bigcap_{h\in V(\Sigma_S,r)}\mathrm{supp}(h)\ \text{ for every transcript } r \text{ of } \Sigma_S \text{ realizable with respect to } V(S).
--   $$
--
--   This is the paper's main result: it answers Valiant's question of which sequences of concept classes are learnable in his model, for every sequence, with randomized and adaptive learners and arbitrary compatible distributions. The strategy depends on $S$; the polynomial does not depend on $d$ or $S$.
--
--   Differences from the source:
--   - encoding: size poly(d) → depth ≤ `C * d ^ k` with `C k : ℕ` chosen before d and S; reason: for d ≥ 1 a monomial bound is equivalent to a polynomial bound
--   - encoding: poly(d, 1/ε, 1/δ) → `C * (d / (ε * δ)) ^ k`; reason: for d, 1/ε, 1/δ ≥ 1 this is equivalent to a polynomial bound
--   - encoding: every response transcript r realizable with respect to V(S) → the transcript of Σ_S on each `h₀ ∈ V(S)`; reason: footnote 3 defines realizable in this way
--   - encoding: a randomized learner with internal randomness → a `PMF` over deterministic protocols on each input (`Learner`); reason: fixing the internal randomness gives a deterministic protocol (p.15), and with a bounded budget on a finite domain only finitely many protocols are distinct; no learner is lost
--   - encoding: at most m(d, ε, δ) positive examples and membership queries → at most m(d, ε, δ) calls on each oracle, on every path of every protocol in the support (`WithinBudget`); reason: this is the paper's own count (Remark 3.1, p.15; proof of Theorem 4.10, p.28)
--   - encoding: d ∈ N, with the sequence starting at H₁ → `1 ≤ d`; reason: the sequence is indexed from 1; `H 0` is not part of the source
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.3 (PDF p.5), Theorem 1.1; restated pp.17 and 30 (PDF pp.19 and 32)

import Mathlib
import Definitions.Def_ValiantModel_Learnable
import Definitions.Def_ValiantModel_IsCompressionScheme

namespace ValiantModel

/-- **Theorem 1.1 (Characterization)**, arXiv:2605.13840 (version held), p.3 (PDF p.5), restated
pp.17 and 30 (PDF pp.19 and 32). A sequence of concept classes is learnable in Valiant's model if
and only if every realizable positive sample `S ⊆ {0,1}^d` admits an adaptive-query compression
scheme of size `poly(d)`.

**Formalization Note.** `poly(d)` is `C * d ^ k`, equivalent to any polynomial bound since `d ≥ 1`.
The polynomial is chosen before `d` and `S`, the strategy after `S`. A realizable positive sample is
an `S` with `V(S) ≠ ∅`; `S = ∅` is included. -/
theorem theorem_1_1_characterization (H : ConceptSequence) :
    Learnable H ↔
      ∃ C k : ℕ, ∀ d : ℕ, 1 ≤ d → ∀ S : Finset (Point d), (positiveVS (H d) S).Nonempty →
        ∃ σS : Strategy d, σS.depth ≤ C * d ^ k ∧ IsCompressionScheme (H d) S σS := by sorry

end ValiantModel
