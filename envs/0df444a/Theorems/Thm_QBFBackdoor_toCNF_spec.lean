-- Prove2me | Theorems.Thm_QBFBackdoor_toCNF_spec
-- name    : QBFBackdoor.toCNF_spec
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:04.404194+00:00
-- url     : https://prove2.me/theorems/1187dec7-f69e-4918-bbde-406953d86cd7
-- title:
--   Proof of Theorem 5.9 — $\Gamma_{\mathrm{AFF}}$ converts to 2-CNF $\cap$ HORN
-- statement:
--   Let $\phi$ be a $\Gamma_{\mathrm{AFF}}$ formula and let $\mathrm{cnf}(\phi)$ replace every equality $(x=y)$ by $(x\vee\neg y)\wedge(\neg x\vee y)$ and every unit atom by the equivalent unit clause. Then:
--
--   1. an assignment satisfies $\phi$ if and only if it satisfies every clause of $\mathrm{cnf}(\phi)$;
--   2. every clause of $\mathrm{cnf}(\phi)$ has at most two literals and at most one positive literal, so $\mathrm{cnf}(\phi)\in$ 2-CNF $\cap$ HORN.
--
--   Applied to each disjunct, it turns a 4-Disjunct-QBF$(\Gamma_{\mathrm{AFF}})$ formula into a disjunction of four formulas in 2-CNF $\cap$ HORN with the same truth value.
--
--   Differences from the source:
--   - encoding: the conversion applied to a formula with matrix in 4-Disjunct-ΓAFF → the conversion of one disjunct ϕ; reason: the conversion acts on each disjunct separately
--   - encoding: variables x1, …, xn and prefix Q1x1 … Qnxn → variables Fin n quantified in index order, q j = true meaning ∃; reason: relabelling; same formulas
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of Theorem 5.9, p.26

import Mathlib
import Definitions.Def_QBFBackdoor_toCNF

namespace QBFBackdoor

/-- **Conversion of `Γ_AFF` to 2-CNF ∩ HORN.** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean
Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), proof of Theorem 5.9, p.26: "For CNF classes,
take a quantified formula with matrix in 4-Disjunct-ΓAFF, and replace every atom of the form
(x = y) with a conjunction of clauses (x∨¬y)∧(¬x∨y), and unit atoms with equivalent unit clauses.
Observe that the resulting formula is a disjunction of 4 formulas in 2-CNF ∩ HORN".

For every `Γ_AFF` formula `ϕ`: an assignment satisfies `ϕ` iff it satisfies every clause of
`toCNF ϕ`, and every clause of `toCNF ϕ` has at most two literals and at most one positive
literal.

**Formalization Note** Stated per disjunct; the disjunction of four converted disjuncts is
then a disjunction of four formulas in 2-CNF ∩ HORN. -/
theorem toCNF_spec {n : ℕ} (ϕ : List (GAtom n)) :
    (∀ a : Fin n → Bool, SatAll ϕ a ↔ ∀ c ∈ toCNF ϕ, ∃ l ∈ c, a l.1 = l.2) ∧
    (∀ c ∈ toCNF ϕ, c.card ≤ 2 ∧ (c.filter (fun l => l.2 = true)).card ≤ 1) := by sorry

end QBFBackdoor
