-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_deficiency_supermodular
-- name    : RandomCNFDeficiency.LowerBound.deficiency_supermodular
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T17:51:05.267438+00:00
-- url     : https://prove2.me/theorems/2c8e742a-fd32-417e-9661-c8d97368e4c2
-- title:
--   Supermodularity of finite clause matching deficiency (Equation 15)
-- statement:
--   Let $A,B$ be finite sets of signed clauses on $n$ Boolean variables, and let $T$ be any subset of those variables. Write $N(A)$ for the variables occurring in $A$ and define the matching deficiency by $h_T(A)=|A|-|N(A)\setminus T|$. Then
--
--   $$h_T(A)+h_T(B)\le h_T(A\cup B)+h_T(A\cap B).$$
--
--   This supermodularity inequality is the structural step behind the existence of a largest deficiency-maximizing closure and its monotonicity. It is independent of satisfiability, clause widths, expansion conditions and admissibility thresholds.
-- source:
--   Jonas Conneryd, STOC 2027 submission #332, October 2026, Section 3.1, Equation (15) in the proof of Lemma 3.2, printed p. 9 / PDF p. 11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
open RandomCNFDeficiency.LowerBound

theorem RandomCNFDeficiency.LowerBound.deficiency_supermodular {n : ℕ} (T : Finset (Fin n)) (A B : CNF n) :
    deficiency T A + deficiency T B ≤ deficiency T (A ∪ B) + deficiency T (A ∩ B) := by sorry
