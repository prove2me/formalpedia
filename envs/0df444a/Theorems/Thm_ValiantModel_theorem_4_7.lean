-- Prove2me | Theorems.Thm_ValiantModel_theorem_4_7
-- name    : ValiantModel.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:10.079116+00:00
-- url     : https://prove2.me/theorems/34158d91-d828-453e-b801-057714abadec
-- title:
--   Theorem 4.7, p.22 — existence of weak query-based compression schemes (corrected: $\max(m_W,1)$)
-- statement:
--   Let $L$ be a learner with sample/query complexity $m_W$. For every $d\ge 1$ and every nonempty finite set $S\subseteq\{0,1\}^d$ with $V(S)\neq\emptyset$, there is a weak query-based compression scheme $\sigma_S$ for $S$ making at most $q_d$ membership queries, where one may take
--
--   $$
--   q_d=\max\Bigl(m_W\bigl(d,\tfrac1{18},\tfrac13\bigr),1\Bigr)\cdot O\bigl(d\,\mathrm{VC}(H_d)\bigr).
--   $$
--
--   A single short adaptive certificate therefore covers a third of any realizable positive sample, whichever realizable target answers the queries. The constant $C$ in the $O(\cdot)$ is absolute. The proof uses the published Sauer–Shelah lemma to bound $\log_2|H_d|$ by $O(d\,\mathrm{VC}(H_d))$.
--
--   Differences from the source:
--   - correction: mW(d, 1/18, 1/3) · O(d VC(Hd)) → `max(mW(d, 1/18, 1/3), 1) · O(d VC(Hd))`; reason: the printed bound is false at mW = 0. Hd = {all-one, all-zero} for every d, with the learner outputting all-one with no oracle call, is a valid learner with mW ≡ 0, since the all-zero target has no compatible distribution. For S = {x} the bound gives depth 0, but a depth-0 strategy has V(σ, r) = Hd, whose intersection of supports is empty. The proof's own "Choose q_d ≥ 1" contradicts display (3) exactly here
--   - generalization: H learnable, with mW the complexity of a witnessing learner, polynomial → any learner `L` with any complexity function (`HasComplexity`), no polynomial bound; reason: the argument does not use the polynomial bound; `Learnable` supplies such an `L` and `m`, so the printed statement is the special case
--   - encoding: O(·) → an absolute constant `C > 0`, quantified before the class, the learner and d; reason: the standard meaning of O(·); it depends on nothing
--   - encoding: VC(Hd) → `(vcDim (H d)).toNat`; reason: vcDim is finite on the finite domain (checked in the sanity file), so `toNat` loses nothing
--   - encoding: a randomized learner with internal randomness → a `PMF` over deterministic protocols on each input (`Learner`); reason: fixing the internal randomness gives a deterministic protocol (p.15), and with a bounded budget on a finite domain only finitely many protocols are distinct; no learner is lost
--   - encoding: at most m(d, ε, δ) positive examples and membership queries → at most m(d, ε, δ) calls on each oracle, on every path of every protocol in the support (`WithinBudget`); reason: this is the paper's own count (Remark 3.1, p.15; proof of Theorem 4.10, p.28)
--   - encoding: d ∈ N, with the sequence starting at H₁ → `1 ≤ d`; reason: the sequence is indexed from 1; `H 0` is not part of the source
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.22 (PDF p.24), Theorem 4.7 and display (3); uses Sauer–Shelah, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_ValiantModel_Learnable
import Definitions.Def_ValiantModel_IsWeakScheme

open HighDimProb.Chaining

namespace ValiantModel

/-- **Theorem 4.7 (Existence of Weak Query-Based Compression Schemes)**, arXiv:2605.13840 (version
held), p.22 (PDF p.24), **corrected**. Every nonempty `S` with `V(S) ≠ ∅` has a weak scheme making at
most `q_d = max(mW(d, 1/18, 1/3), 1) · O(d VC(Hd))` membership queries (display (3)).

**Formalization Note.** The print has `mW` where this has `max(mW, 1)`. It is false with `mW = 0`:
for `Hd = {all-one, all-zero}` and the learner outputting all-one with no call, `S = {x}` needs one
query, while the printed bound is `0`. `O(·)` is an absolute constant `C`, quantified before the
class and the learner. `VC(Hd)` is the `toNat` of `vcDim`, which is finite on the finite domain. -/
theorem theorem_4_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ConceptSequence) (L : Learner) (mW : ℕ → ℝ → ℝ → ℕ),
      HasComplexity H L mW →
      ∀ d : ℕ, 1 ≤ d → ∀ S : Finset (Point d), S.Nonempty → (positiveVS (H d) S).Nonempty →
        ∃ σ : Strategy d,
          (σ.depth : ℝ) ≤
            (max (mW d (1 / 18) (1 / 3)) 1 : ℕ) * (C * ((d : ℝ) * ((vcDim (H d)).toNat : ℝ))) ∧
          IsWeakScheme (H d) S σ := by sorry

end ValiantModel
