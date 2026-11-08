-- Prove2me | Theorems.Thm_ValiantModel_theorem_4_6
-- name    : ValiantModel.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:08.843952+00:00
-- url     : https://prove2.me/theorems/193936b1-aa35-4679-834b-0c69a3f13f30
-- title:
--   Theorem 4.6, p.21 — learnability implies query-based compression (corrected: $\max(m_W,1)$)
-- statement:
--   Let $L$ be a learner with sample/query complexity $m_W$. For every $d\ge 1$ there is a number $q_d$ with
--
--   $$
--   q_d\le\max\Bigl(m_W\bigl(d,\tfrac1{18},\tfrac13\bigr),1\Bigr)\cdot O\bigl(d\,\mathrm{VC}(H_d)\bigr)
--   $$
--
--   such that every nonempty finite set $S\subseteq\{0,1\}^d$ with $V(S)\neq\emptyset$ has a weak scheme of depth at most $q_d$, as in Theorem 4.7, and an adaptive-query compression scheme $\Sigma_S$ of size at most
--
--   $$
--   q_d\cdot\bigl(1+\lceil\log_{3/2}|S|\rceil\bigr).
--   $$
--
--   This gives the direction from learnability to compression in Theorem 1.1, with a size logarithmic in $|S|$ and at most polynomial in $d$ when $m_W$ and $\mathrm{VC}(H_d)$ are.
--
--   Differences from the source:
--   - correction: mW(d, 1/18, 1/3) · O(d VC(Hd)) → `max(mW(d, 1/18, 1/3), 1) · O(d VC(Hd))`; reason: the printed bound is false at mW = 0. Hd = {all-one, all-zero} for every d, with the learner outputting all-one with no oracle call, is a valid learner with mW ≡ 0, since the all-zero target has no compatible distribution. For S = {x} the bound gives depth 0, but a depth-0 strategy has V(σ, r) = Hd, whose intersection of supports is empty. The proof's own "Choose q_d ≥ 1" contradicts display (3) exactly here
--   - generalization: H learnable, with mW the complexity of a witnessing learner, polynomial → any learner `L` with any complexity function (`HasComplexity`), no polynomial bound; reason: the argument does not use the polynomial bound; `Learnable` supplies such an `L` and `m`, so the printed statement is the special case
--   - generalization: q_d is as in Theorem 4.7 → the Lean also asserts that every such S has a weak scheme (Definition 13) of depth at most q_d; reason: this is what "q_d as in Theorem 4.7" asks of q_d; dropping that conjunct gives the printed statement
--   - encoding: O(·) → an absolute constant `C > 0`, quantified before the class, the learner and d; reason: the standard meaning of O(·); it depends on nothing
--   - encoding: VC(Hd) → `(vcDim (H d)).toNat`; reason: vcDim is finite on the finite domain (checked in the sanity file), so `toNat` loses nothing
--   - encoding: a randomized learner with internal randomness → a `PMF` over deterministic protocols on each input (`Learner`); reason: fixing the internal randomness gives a deterministic protocol (p.15), and with a bounded budget on a finite domain only finitely many protocols are distinct; no learner is lost
--   - encoding: at most m(d, ε, δ) positive examples and membership queries → at most m(d, ε, δ) calls on each oracle, on every path of every protocol in the support (`WithinBudget`); reason: this is the paper's own count (Remark 3.1, p.15; proof of Theorem 4.10, p.28)
--   - encoding: d ∈ N, with the sequence starting at H₁ → `1 ≤ d`; reason: the sequence is indexed from 1; `H 0` is not part of the source
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.21 (PDF p.23), Theorem 4.6

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_ValiantModel_Learnable
import Definitions.Def_ValiantModel_IsWeakScheme
import Definitions.Def_ValiantModel_IsCompressionScheme

open HighDimProb.Chaining

namespace ValiantModel

/-- **Theorem 4.6 (Learnability Implies Query-Based Compression)**, arXiv:2605.13840 (version held),
p.21 (PDF p.23), **corrected**. There is `q_d ≤ max(mW(d, 1/18, 1/3), 1) · O(d VC(Hd))`, as in
Theorem 4.7 (it bounds the weak schemes), such that every nonempty `S` with `V(S) ≠ ∅` has a scheme
(Definition 2) of size at most `q_d · (1 + ⌈log_{3/2} |S|⌉)`.

**Formalization Note.** The print has `mW` where this has `max(mW, 1)`, for the reason in
`theorem_4_7`. `q_d` comes before `S`. `O(·)` is an absolute constant `C`, quantified before the
class and the learner. `S` is nonempty, so the logarithm of `|S|` is a true nonnegative value. -/
theorem theorem_4_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ConceptSequence) (L : Learner) (mW : ℕ → ℝ → ℝ → ℕ),
      HasComplexity H L mW →
      ∀ d : ℕ, 1 ≤ d → ∃ qd : ℕ,
        (qd : ℝ) ≤
          (max (mW d (1 / 18) (1 / 3)) 1 : ℕ) * (C * ((d : ℝ) * ((vcDim (H d)).toNat : ℝ))) ∧
        ∀ S : Finset (Point d), S.Nonempty → (positiveVS (H d) S).Nonempty →
          (∃ σ : Strategy d, σ.depth ≤ qd ∧ IsWeakScheme (H d) S σ) ∧
          ∃ σS : Strategy d,
            σS.depth ≤ qd * (1 + ⌈Real.logb (3 / 2) (S.card : ℝ)⌉₊) ∧
            IsCompressionScheme (H d) S σS := by sorry

end ValiantModel
