-- Prove2me | Theorems.Thm_QBFBackdoor_theorem_1_1
-- name    : QBFBackdoor.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:41.778864+00:00
-- url     : https://prove2.me/theorems/13bfaec1-ff84-458e-a8dc-2c400aaffc93
-- title:
--   Theorem 1.1 (= Theorem 5.9) — QBF is PSPACE-hard with a supplied backdoor of size two to 2-CNF, HORN or AFF
-- statement:
--   For a class $\mathcal C\in\{\text{2-CNF},\ \text{HORN},\ \text{AFF}\}$, QBF parameterized by the size of a strong backdoor to QBF$(\mathcal C)$ is **para-PSPACE-hard**: already the slice of parameter value at most $2$ is PSPACE-hard. Hardness also holds when a backdoor of size two is supplied with the input. Precisely, for each of the three classes the following two languages are PSPACE-hard under polynomial-time many-one reductions:
--
--   1. the true QBFs $\Phi$ that have a strong backdoor $B$ to QBF$(\mathcal C)$ with $|B|\le2$;
--   2. the pairs $(\Phi,B)$ of a true QBF $\Phi$ and a strong backdoor $B$ to QBF$(\mathcal C)$ with
--   $$
--   |B|=2 .
--   $$
--
--   For 2-CNF and HORN the instances are CNF QBFs. For AFF they are QBFs whose atoms are affine equations with clausal guards, $\bigl(\bigoplus_{v\in A}x_v=b\bigr)\vee T$. Clauses and guards contain no complementary pair.
--
--   For SAT, a backdoor of size $b$ to these classes reduces evaluation to $2^b$ polynomial-time subproblems. The theorem shows that for QBF the backdoor size alone gives no such gain: the problem is as hard as general QBF already at $b=2$, and the obstruction is evaluation, not finding the backdoor.
--
--   Differences from the source:
--   - generalization: para-PSPACE-hard: there exists a constant c ≥ 0 such that the slice k ≤ c is PSPACE-hard → the slice with the explicit constant c = 2 is PSPACE-hard; reason: an explicit witness for the existential c; it implies para-PSPACE-hardness
--   - reading: Theorem 1.1 (minimum backdoor size as parameter) together with "hardness holds even when this backdoor is supplied with the input" (p.3) and Theorem 5.9 ("PSPACE-hard for backdoors to C of size 2") → both languages, the slice (∃ B, |B| ≤ 2, B a strong backdoor) ∧ true and the supplied form |B| = 2 ∧ B a strong backdoor ∧ true, for each of the three classes; reason: neither language's hardness implies the other's, and the paper asserts both
--   - reading: QBF with a backdoor to AFF → QBFs with guarded affine atoms (⊕A = b) ∨ T; reason: the representation the paper uses for the affine target (Lemma 4.4, p.21; "Section 4 makes the encoding conventions explicit", p.3); Theorem 5.9 derives the AFF case from 4-Disjunct-QBF(ΓAFF) through these guarded equality atoms ("For the affine target, keeping the guarded equality atoms gives affine equations after restriction", p.21), whereas a residual CNF clause is affine only when it has at most one literal
--   - reading: Input clauses have no repeated literals or complementary pair; tautological clauses are removed (p.16) → clauses and guards with a complementary pair make an input a no-instance (NonTaut conjunct); reason: the paper's input domain; strings outside it are not instances
--   - encoding: PSPACE-hard (standard machine model, instances as strings) → the published OptimalQueuingComplexity.Restless.PSPACEHard (every PSPACE language reduces by a Mathlib TM2 polynomial-time map) on structural injective bit encodings; reason: the standard notions; the encodings are injective and of length polynomial in ∥Φ∥, so no instance changes
--   - encoding: variables x1, …, xn and prefix Q1x1 … Qnxn → variables Fin n quantified in index order, q j = true meaning ∃; reason: relabelling; same formulas
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), Theorem 1.1, p.2, with p.3; Theorem 5.9, p.26; para-PSPACE-hardness, §3.3, p.17

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_QBFBackdoor_encCNF

namespace QBFBackdoor

open MDPComplexity.PartiallyObserved OptimalQueuingComplexity.Restless

/-- **Theorem 1.1 (= Theorem 5.9).** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean
Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), p.2: "If C is 2-CNF, HORN, or AFF then QBF is
para-PSPACE-hard parameterized by the backdoor size to QBF(C)." p.3: "Our reduction produces a
backdoor of size two, and hardness holds even when this backdoor is supplied with the input."
Theorem 5.9, p.26: "If C is 2-CNF, HORN, or AFF then QBF is PSPACE-hard for backdoors to C of
size 2." "Para-PSPACE-hard" (p.17): "there exists a constant c ≥ 0 such that the slice
{x | (x, k) ∈ X, k ≤ c} is PSPACE-hard."

For each of the three classes, two languages are PSPACE-hard under polynomial-time many-one
reductions:
1. (the slice `c = 2`) true QBFs having a strong backdoor of size at most two to the class;
2. (supplied backdoor) pairs of a true QBF and a set `B` of exactly two variables that is a strong
   backdoor to the class.
For 2-CNF and HORN the instances are CNF QBFs; for AFF they are QBFs with guarded affine atoms
`(⊕E = b) ∨ T`, the representation of Lemma 4.4 (p.21).

**Formalization Note** PSPACE-hardness is the published `PSPACEHard` on Mathlib TM2 machines;
instances are encoded by the structural, injective encodings `encCNF`, `encCNFB`, `encGAff`,
`encGAffB`. Variables are `Fin n` quantified in index order, `true` = ∃. Backdoor membership is
syntactic and atom by atom, deleting only atoms made true (Definition 3.4, p.17; p.16). Inputs
satisfy the clause convention of p.16 (no complementary pair), and instances violating it are
no-instances. -/
theorem theorem_1_1 :
    PSPACEHard encCNF (fun I : CNFInst => NonTaut I.φ ∧
      (∃ B : Finset (Fin I.n), B.card ≤ 2 ∧ IsBackdoor2CNF I.φ B) ∧ I.φ.holds) ∧
    PSPACEHard encCNFB (fun I : CNFInstB => NonTaut I.φ ∧
      I.B.card = 2 ∧ IsBackdoor2CNF I.φ I.B ∧ I.φ.holds) ∧
    PSPACEHard encCNF (fun I : CNFInst => NonTaut I.φ ∧
      (∃ B : Finset (Fin I.n), B.card ≤ 2 ∧ IsBackdoorHorn I.φ B) ∧ I.φ.holds) ∧
    PSPACEHard encCNFB (fun I : CNFInstB => NonTaut I.φ ∧
      I.B.card = 2 ∧ IsBackdoorHorn I.φ I.B ∧ I.φ.holds) ∧
    PSPACEHard encGAff (fun I : GAffInst => I.ψ.NonTaut ∧
      (∃ B : Finset (Fin I.n), B.card ≤ 2 ∧ IsBackdoorAff I.ψ B) ∧ I.ψ.holds) ∧
    PSPACEHard encGAffB (fun I : GAffInstB => I.ψ.NonTaut ∧
      I.B.card = 2 ∧ IsBackdoorAff I.ψ I.B ∧ I.ψ.holds) := by sorry

end QBFBackdoor
