-- Prove2me | Theorems.Thm_RevRedSAT_lemma_4_8
-- name    : RevRedSAT.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:11.164567+00:00
-- url     : https://prove2.me/theorems/c1d7924d-8a7b-44c0-8c43-3d2e5255a3a7
-- title:
--   Lemma 4.8 — recovering an assignment with s decision or parity queries
-- statement:
--   Let $\varphi$ be a CNF formula over $n$ variables and $X$ a set of $s$ of its variables. A query substitutes constants for some variables of $\varphi$ and asks about the restricted formula.
--
--   1. There is an adaptive strategy of $s$ decision queries whose final partial assignment fixes exactly the variables of $X$ and such that, for every satisfiable $\varphi$, when every query is answered truthfully (is the restricted formula satisfiable?), the final restricted formula is satisfiable.
--   2. There is an adaptive strategy of $s$ parity queries with the same shape such that, for every $\varphi$ with an odd number of satisfying assignments, truthful answers (is the number of satisfying extensions odd?) lead to a final restriction with an odd number of satisfying extensions.
--   3. Substituting constants into $\varphi$ never increases its number of occurring variables, its number of distinct clauses, its number of clauses or its width.
--
--   Self-reduction turns the decision (or parity) algorithm into a search algorithm at the cost of $s$ further queries of no larger size.
--
--   **Formalization Note** The strategy is fixed before the formula: it depends on $n$ and $X$ only.
--
--   Differences from the source:
--   - reading: at most s decision (parity) queries suffice to assign all variables in X → there is an adaptive strategy, chosen before the formula, of exactly s queries that works for every formula; reason: a strategy chosen after the formula could name a good assignment without querying, which makes the statement empty; the proof's strategy depends only on X
--   - encoding: a query is a formula obtained by substitution → a query is a partial assignment; the queried formula is the restriction of φ by it; reason: the restriction is exactly the substituted formula of the proof
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 4.8, p.34 (printed) = PDF p.36

import Mathlib
import Definitions.Def_RevRedSAT_restrict

set_option autoImplicit false

namespace RevRedSAT

open Classical in
/-- **Lemma 4.8 (solution recovery by self-reduction).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 4.8, p.34: "Let F be a CNF formula, and let X be a specified set of s variables of F.
1. If F is satisfiable, at most s decision queries suffice to assign all variables in X so that the
resulting restricted formula remains satisfiable. 2. If F has an odd number of satisfying
assignments, at most s parity queries suffice to assign all variables in X so that the resulting
restricted formula still has an odd number of satisfying assignments. Every query is obtained by
substituting constants for some variables of F. Its variable count, clause count, and clause width
are no greater than those of F."

For every set `X` of `s` variables:
1. there is an adaptive strategy of `s` queries, each query the formula with constants substituted
   for some variables, whose final partial assignment fixes exactly the variables of `X` and, for
   every satisfiable `φ` and truthful decision answers, leaves `φ` satisfiable;
2. there is such a strategy which, for every `φ` with an odd number of satisfying assignments and
   truthful parity answers (parity of the number of satisfying extensions), leaves an odd number of
   satisfying extensions;
3. substituting constants never increases the number of occurring variables, the number of distinct
   clauses, the number of clauses, or the width.

**Formalization Note** The strategy is chosen before the formula (it depends only on `n` and `X`);
a strategy chosen after `φ` could simply name a good assignment, which would make the statement
empty. Exactly `s` queries are made, which is "at most `s`". A parity query on the restricted
formula counts assignments of its unfixed variables (proof, p.34). -/
theorem lemma_4_8 (n : ℕ) (X : Finset (Fin n)) :
    (∃ σ : QueryStrategy n, (∀ h i, (σ.final h i).isSome ↔ i ∈ X) ∧
      ∀ φ : MainResults.CNF n, MainResults.Satisfiable φ →
        MainResults.Satisfiable (restrict φ (σ.final (runAnswers σ
          (fun ρ => decide (MainResults.Satisfiable (restrict φ ρ))) X.card)))) ∧
    (∃ σ : QueryStrategy n, (∀ h i, (σ.final h i).isSome ↔ i ∈ X) ∧
      ∀ φ : MainResults.CNF n, Odd (numExt φ fun _ => none) →
        Odd (numExt φ (σ.final (runAnswers σ (fun ρ => decide (Odd (numExt φ ρ))) X.card)))) ∧
    (∀ (φ : MainResults.CNF n) (ρ : Fin n → Option Bool),
      occVars (restrict φ ρ) ≤ occVars φ ∧ distinctClauses (restrict φ ρ) ≤ distinctClauses φ ∧
      (restrict φ ρ).length ≤ φ.length ∧ width (restrict φ ρ) ≤ width φ) := by sorry

end RevRedSAT
