-- Prove2me | Theorems.Thm_QBFBackdoor_round_equivalence
-- name    : QBFBackdoor.round_equivalence
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:32.10831+00:00
-- url     : https://prove2.me/theorems/826d11fa-c6ec-4cc5-81b0-38ecc75b8439
-- title:
--   §5.2 — one balanced round preserves truth
-- statement:
--   Fix an assignment to the variables of the current prefix. Let $b$ range over finitely many batches. Each batch has a truth value $D_b$ (its original disjunction), private existential variables $A_b$, private universal variables $W_b$, and a squished matrix $F_b$ with
--
--   $$
--   D_b \iff \exists A_b\,\forall W_b.\ F_b .
--   $$
--
--   Let $D_{\mathrm{carry}}$ be the carried disjuncts, which mention none of these variables. Then
--
--   $$
--   \bigvee_b D_b \vee D_{\mathrm{carry}} \iff \exists \bigcup_b A_b\ \forall \bigcup_b W_b.\ \Bigl(\bigvee_b F_b\vee D_{\mathrm{carry}}\Bigr).
--   $$
--
--   So all batches of a round can be squished in parallel, adding only one existential and one universal block per round.
--
--   Differences from the source:
--   - generalization: batches of squished ΓAFF matrices under a fixed assignment to the current prefix → an arbitrary finite family of truth values D b and predicates F b on private Boolean assignment spaces; reason: the argument uses only the stated equivalences and the privacy of the variables; the round of §5.2 is a special case
--   - encoding: fresh private variable sets Ab, Wb and carried disjuncts not containing them → separate arguments x b : Fin (a b) → Bool, y b : Fin (w b) → Bool for each batch, and a proposition Dc independent of them; reason: privacy is the independence of the arguments; the spaces stay Boolean, hence nonempty
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), §5.2, p.25

import Mathlib

namespace QBFBackdoor

/-- **One balanced round preserves truth.** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean
Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…), §5.2, p.25: "For each batch b, let Db be its
original disjunction and let Fb be its squished matrix, with fresh existential variables Ab and
universal variables Wb. The pointwise proof of Lemma 5.7 gives Db ⇐⇒ ∃Ab∀Wb.Fb. All existential
variables of the round can be placed in one block, followed by one block containing all its
universal variables. … Therefore ⋁_b Db ∨ Dcarry ⇐⇒ ∃ ⋃_b Ab ∀ ⋃_b Wb. (⋁_b Fb ∨ Dcarry)."

For a fixed assignment to the current prefix: given finitely many batches `b`, each with truth
value `D b`, private Boolean existential variables `A_b` (`a b` of them), private Boolean universal
variables `W_b` (`w b` of them) and squished matrix `F b` with `D b ⇔ ∃A_b ∀W_b. F b`, and a carried
part `D_carry` not mentioning these variables, the disjunction of the `D b` and `D_carry` is
equivalent to `∃ ⋃A_b ∀ ⋃W_b. (⋁ F b ∨ D_carry)`.

**Formalization Note** Stated abstractly over the batch index type `β` (finite) and the truth
values, for a fixed assignment to the original variables (the paper's "fix an assignment to all
variables of the current prefix"). The assignment spaces are kept Boolean, `Fin (a b) → Bool`:
they are nonempty, as the argument needs. -/
theorem round_equivalence (β : Type) [Fintype β] (a w : β → ℕ) (D : β → Prop)
    (F : ∀ b, (Fin (a b) → Bool) → (Fin (w b) → Bool) → Prop) (Dc : Prop)
    (hD : ∀ b, D b ↔ ∃ x, ∀ y, F b x y) :
    ((∃ b, D b) ∨ Dc) ↔
      ∃ x : ∀ b, Fin (a b) → Bool, ∀ y : ∀ b, Fin (w b) → Bool,
        (∃ b, F b (x b) (y b)) ∨ Dc := by sorry

end QBFBackdoor
