-- Prove2me | Theorems.Thm_QBFBackdoor_qbf3_falsity_pspaceComplete
-- name    : QBFBackdoor.qbf3_falsity_pspaceComplete
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:47.624263+00:00
-- url     : https://prove2.me/theorems/876d3231-6f4a-443e-8802-4bbd50c6a774
-- title:
--   Proof of Lemma 5.4 (cited) — falsity of quantified 3-CNF is PSPACE-complete
-- statement:
--   Let $\mathrm{FALSE}_3$ be the set of quantified CNF formulas $\Phi=Q.(C_1\wedge\cdots\wedge C_m)$ whose clauses have at most three literals (and contain no complementary pair) and which are **false**. Then
--
--   $$
--   \mathrm{FALSE}_3 \text{ is PSPACE-complete}
--   $$
--
--   under polynomial-time many-one reductions. The paper uses this classical fact (Stockmeyer and Meyer, 1973, together with the closure of PSPACE under complement) as the starting point of its reduction. It is not proved in the paper.
--
--   Differences from the source:
--   - encoding: PSPACE-complete → the published OptimalQueuingComplexity.Restless.PSPACEComplete (membership by a polynomial-space Mathlib TM2 machine, hardness by TM2 polynomial-time reductions) for the injective encoding encCNF; reason: the standard notions
--   - reading: quantified 3-CNF formula → CNF QBF whose clauses (sets of literals) have at most three literals and no complementary pair; reason: p.14 defines d-CNF by at most d literals per clause; p.16 fixes that input clauses have no complementary pair
--   - encoding: variables x1, …, xn and prefix Q1x1 … Qnxn → variables Fin n quantified in index order, q j = true meaning ∃; reason: relabelling; same formulas
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of Lemma 5.4, p.23

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_QBFBackdoor_encCNF

namespace QBFBackdoor

open MDPComplexity.PartiallyObserved OptimalQueuingComplexity.Restless

/-- **Falsity of quantified 3-CNF is PSPACE-complete** (cited). Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean
Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of Lemma 5.4, p.23:
"Falsity of quantified 3-CNF is PSPACE-complete because PSPACE is closed under complement."
(Stockmeyer–Meyer 1973.)

The language of encoded CNF QBFs whose clauses have at most three literals (and no complementary
pair) and which are false is in PSPACE and PSPACE-hard under polynomial-time many-one reductions.

**Formalization Note** PSPACE and PSPACE-hardness are the published
`OptimalQueuingComplexity.Restless.PSPACEComplete` on Mathlib TM2 machines. Instances are the
published CNF `QBF n m` (variables `Fin n` quantified in index order, `true` = ∃, clauses sets of
literals) under the structural encoding `encCNF`. The no-complementary-pair condition is the
paper's input convention (p.16). -/
theorem qbf3_falsity_pspaceComplete :
    PSPACEComplete encCNF (fun I : CNFInst =>
      NonTaut I.φ ∧ (∀ i, (I.φ.clause i).card ≤ 3) ∧ ¬ I.φ.holds) := by sorry

end QBFBackdoor
