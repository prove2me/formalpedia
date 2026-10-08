-- Prove2me | Theorems.Thm_QLLL_SAT_card_inter_mul_card
-- name    : QLLL.SAT.card_inter_mul_card
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:05.548652+00:00
-- url     : https://prove2.me/theorems/597f2c44-18b4-4296-96cf-8074c40a4b6e
-- title:
--   Events depending on complementary sets of variables are independent
-- statement:
--   Let $V$ be a natural number and $S \subseteq \{1, \dots, V\}$. Let $A, B$ be sets of assignments in $\{0,1\}^{V}$ such that membership in $A$ depends only on the values of the variables in $S$, and membership in $B$ depends only on the values of the variables outside $S$. Then
--   $$|A \cap B| \cdot 2^{V} \ =\ |A| \cdot |B|,$$
--   that is, $\Pr(A \cap B) = \Pr(A)\Pr(B)$ under the uniform distribution.
--
--   This is the classical counterpart of Lemma 11 of Ambainis, Kempe and Sattath (constraints on disjoint sets of qubits are independent). It shows that clauses sharing no variables are mutually independent, which provides the dependency graph in the proof of Corollary 2.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), classical counterpart of Lemma 11, used in Corollary 2

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Mathlib
import Std.Sat.CNF

open QLLL
open QLLL.SAT
open Finset Std.Sat
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
variable {V : ℕ}

theorem QLLL.SAT.card_inter_mul_card {S : Finset (Fin V)} {A B : Finset (Asg V)}
    (hA : DependsOn S A) (hB : DependsOn Sᶜ B) :
    (A ∩ B).card * Fintype.card (Asg V) = A.card * B.card := by sorry
