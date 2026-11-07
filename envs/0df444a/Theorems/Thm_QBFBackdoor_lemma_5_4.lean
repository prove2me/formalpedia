-- Prove2me | Theorems.Thm_QBFBackdoor_lemma_5_4
-- name    : QBFBackdoor.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:48.136675+00:00
-- url     : https://prove2.me/theorems/f560cddf-9d86-4011-92b8-47101ed98f6e
-- title:
--   Lemma 5.4 — Disjunct-QBF$(\Gamma_{\mathrm{AFF}})$ is PSPACE-complete
-- statement:
--   Let Disjunct-QBF$(\Gamma_{\mathrm{AFF}})$ be the problem of deciding whether a QBF $Q.(\phi_1\vee\cdots\vee\phi_q)$, with any number $q$ of disjuncts, each a conjunction of atoms $(x)$, $(\neg x)$, $(x=y)$, is true. Then
--
--   $$
--   \text{Disjunct-QBF}(\Gamma_{\mathrm{AFF}}) \text{ is PSPACE-complete.}
--   $$
--
--   Each disjunct produced by the hardness reduction has constant size, but the number of disjuncts is unbounded; the rest of §5.2 reduces that number to four.
--
--   Differences from the source:
--   - encoding: PSPACE-complete → the published PSPACEComplete on Mathlib TM2 machines for the injective encoding encDQBF; reason: the standard notions
--   - encoding: q-Disjunct for a positive integer q → any number of disjuncts, zero included; reason: an instance with no disjunct is false (the empty disjunction is ⊥, p.16), so it is a no-instance either way
--   - encoding: variables x1, …, xn and prefix Q1x1 … Qnxn → variables Fin n quantified in index order, q j = true meaning ∃; reason: relabelling; same formulas
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), Lemma 5.4, p.23

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_QBFBackdoor_encCNF

namespace QBFBackdoor

open OptimalQueuingComplexity.Restless

/-- **Lemma 5.4.** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean
Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), p.23: "Disjunct-QBF(ΓAFF) is PSPACE-complete."

The language of encoded disjunctive QBFs over `Γ_AFF` (any number of disjuncts, each a
conjunction of atoms `(x)`, `(¬x)`, `(x = y)`) that are true is in PSPACE and PSPACE-hard.

**Formalization Note** PSPACE-completeness is the published `PSPACEComplete` on Mathlib TM2
machines, for the structural encoding `encDQBF`. An instance with no disjunct is false (the empty
disjunction is `⊥`, p.16), so admitting it changes nothing. -/
theorem lemma_5_4 : PSPACEComplete encDQBF (fun I : DQBFInst => I.Φ.holds) := by sorry

end QBFBackdoor
