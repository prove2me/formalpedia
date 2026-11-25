-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_matching_of_external_hall
-- name    : RandomCNFDeficiency.LowerBound.matching_of_external_hall
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T19:57:39.328965+00:00
-- url     : https://prove2.me/theorems/7c9eabbc-35a3-4cd2-8a27-3b5a4b98620f
-- title:
--   A clause matching avoiding protected variables
-- statement:
--   Let $H$ be a finite family of signed clauses and $S$ a protected variable set. Write $\operatorname{Vars}(C)$ for the variables of a clause and $N(L)=\bigcup_{C\in L}\operatorname{Vars}(C)$. Assume
--
--   $$\forall L\subseteq H,\qquad |L|\le |N(L)\setminus S|.$$
--
--   Then there is an injective map $m:H\to[n]$ satisfying
--
--   $$\forall C\in H,\qquad m(C)\in\operatorname{Vars}(C)\setminus S.$$
--
--   This specialized form of Hall's marriage theorem supplies a clause matching that avoids all protected variables.
-- source:
--   Jonas Conneryd, Random (log n)-CNF Formulas Are Hard for Depth-2 Frege with Modular Gates, manuscript dated November 2, 2026, STOC 2027 submission #332, Lemma 3.5, Hall marriage step, printed pp. 10–11 / PDF pp. 12–13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
open RandomCNFDeficiency.LowerBound

theorem RandomCNFDeficiency.LowerBound.matching_of_external_hall {n : ℕ} (H : CNF n) (S : Finset (Fin n))
    (hH : ∀ L ⊆ H, L.card ≤ (neighborhood L \ S).card) :
    ∃ m : {C // C ∈ H} → Fin n, Function.Injective m ∧
      ∀ C, m C ∈ clauseSupport C.1 ∧ m C ∉ S := by sorry
