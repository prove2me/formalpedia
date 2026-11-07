-- Prove2me | Theorems.Thm_UniqueOptScores_lemma_2_2
-- name    : UniqueOptScores.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:25.040877+00:00
-- url     : https://prove2.me/theorems/46d02c8d-bd03-429c-b599-9ac86aeb4fd4
-- title:
--   Lemma 2.2 — one more score level recognizes $\Psi_r$ with $r+1$ queries
-- statement:
--   Let $X, Y$ be disjoint sets of $N$ points with fixed exterior answers. There is an absolute constant $c$ such that for every $r \ge 1$ there is a score system whose candidates are **all** binary names of one length
--   $$
--   \ell \ \le\ c\,\big(r\,\lfloor\log_2(N+1)\rfloor + \lfloor\log_2(r+1)\rfloor\big),
--   $$
--   with scores in $\{0, \dots, r+1\}$ and at most $r + 1$ queries per candidate on every support, which recognizes, for all occupancies $a = |S \cap X|$, $b = |S \cap Y|$, the predicate
--   $$
--   \Psi_r(a, b) = [a = 1] \lor \big([a \le r] \land [b = 1]\big),
--   $$
--   i.e. $U(S) \iff \Psi_r(|S\cap X|, |S\cap Y|)$ for every support $S \subseteq X \cup Y$. In particular it recognizes $F$ on every support with $|S \cap X| \le r$, with no restriction on $|S \cap Y|$.
--
--   Together with Theorem 2.1 this shows that one additional score level changes the query complexity from at least $N/(24r^3) - 1$ to at most $r + 1$; it supplies the upper memberships of the hierarchy witnesses.
--
--   Differences from the source:
--   - encoding: total deterministic oracle algorithm with scores in {0,…,r} and at most q membership queries (for every support S) → decision trees QTree α ℕ with at most q queried points and score ≤ r under the oracle of every support S ⊆ X ∪ Y (IsScoreSystem); finite nonempty candidate type ι; reason: a total deterministic query algorithm is a decision tree; the bounds are per support as on p.8; same instances
--   - encoding: candidate names of length O(r log(N + 1) + log(r + 1)) → ∃ c absolute (before r, N and the frame) with ℓ ≤ c·(r·Nat.log 2 (N+1) + Nat.log 2 (r+1)); candidates = all of {0,1}^ℓ; reason: O(·) made explicit; floors of base-2 logarithms change only the constant; the full binary domain is the paper's ("exactly one name per candidate in a full binary domain", p.25)
--   - encoding: "recognizes, for all occupancies a, b, the predicate Ψ_r" → U(S) ↔ Ψ_r(|S ∩ X|, |S ∩ Y|) for every support S ⊆ X ∪ Y, plus the clause U(S) ↔ F(S) when |S ∩ X| ≤ r; reason: literal meaning, with the "in particular" clause stated
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Lemma 2.2 (restated), p.25, eq. (4) (stated as Lemma 2.2 in Section 2.3)

import Mathlib
import Definitions.Def_UniqueOptScores_QTree
import Definitions.Def_UniqueOptScores_supportOracle
import Definitions.Def_UniqueOptScores_HasUniqueMax
import Definitions.Def_UniqueOptScores_IsScoreSystem
import Definitions.Def_UniqueOptScores_Fpred
import Definitions.Def_UniqueOptScores_Psi

namespace UniqueOptScores

universe u

/-- **Lemma 2.2 (one more score level suffices).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Lemma 2.2 (restated), p.25: "For every r ≥ 1, an evaluator with scores 0, . . . , r + 1 and
at most r + 1 queries per candidate recognizes, for all occupancies a = |S ∩ X|, b = |S ∩ Y |, the
predicate Ψ_r(a, b) = [a = 1] ∨ ([a ≤ r] ∧ [b = 1]). (4) Candidate names have length
O(r log(N + 1) + log(r + 1)). In particular it recognizes F when a ≤ r, without a restriction on b."

There is an absolute constant `c` such that for every `r ≥ 1` and every frame (`X, Y` disjoint of
size `N`, exterior `e`) there are a name length `ℓ ≤ c·(r⌊log₂(N + 1)⌋ + ⌊log₂(r + 1)⌋)` and a
score system indexed by **all** names `{0,1}^ℓ`, with scores at most `r + 1` and at most `r + 1`
queries on every support, such that on every support `S ⊆ X ∪ Y`, `U(S) ↔ Ψ_r(|S ∩ X|, |S ∩ Y|)`,
and `U(S) ↔ F(S)` whenever `|S ∩ X| ≤ r`.

**Formalization Note.** `O(·)` is an absolute constant `c` quantified before `r`, `N` and the
frame; logarithms are `Nat.log 2` (floors), which changes only the constant. -/
theorem lemma_2_2 :
    ∃ c : ℕ, ∀ r : ℕ, 1 ≤ r → ∀ {α : Type u} [DecidableEq α] (X Y : Finset α) (N : ℕ),
      Disjoint X Y → X.card = N → Y.card = N → ∀ e : α → Bool,
      ∃ ℓ : ℕ, ℓ ≤ c * (r * Nat.log 2 (N + 1) + Nat.log 2 (r + 1)) ∧
        ∃ T : (Fin ℓ → Bool) → QTree α ℕ, IsScoreSystem X Y e T (r + 1) (r + 1) ∧
          (∀ S ⊆ X ∪ Y, HasUniqueMax T (supportOracle X Y e S) ↔
            Psi r (S ∩ X).card (S ∩ Y).card) ∧
          (∀ S ⊆ X ∪ Y, (S ∩ X).card ≤ r →
            (HasUniqueMax T (supportOracle X Y e S) ↔ Fpred X Y S)) := by sorry

end UniqueOptScores
