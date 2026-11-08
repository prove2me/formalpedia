-- Prove2me | Theorems.Thm_ParityCubes_lemma_2_1
-- name    : ParityCubes.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:16:39.235193+00:00
-- url     : https://prove2.me/theorems/e04e2ac1-8ae7-4df2-b834-435b4120ef27
-- title:
--   Lemma 2.1 — the maximal-term rule
-- statement:
--   Let $f$ be a Boolean function with algebraic normal form $f=\sum_A c_Ax_A$. For every set $S$ of variables,
--
--   $$D_Sf=\sum_{A\supseteq S}c_A\,x_{A\setminus S}.$$
--
--   Consequently, for nonempty $S$:
--
--   1. $D_Sf\equiv 1$ if and only if $S$ is a maximal support of $f$;
--   2. $D_Sf\equiv 0$ if and only if no support of $f$ contains $S$.
--
--   This rule translates certificates and zero cubes into statements about the terms of $f$, and all the paper's proofs use it.
--
--   Differences from the source:
--   - encoding: the sum Σ_{A⊇S} c_A x_{A∖S} over F_2 at a point y → the parity of the number of A ⊇ S with c_A = 1 and y_i = 1 for all i ∈ A ∖ S; reason: the definition of the sum over F_2
--   - encoding: the variables x_1,…,x_n → an arbitrary finite type of variables; reason: the same statement; Fin n is an instance
-- source:
--   Sheshadri, Smirnov, The Complexity of Choosing Parity Projections, arXiv:2611.00289 (manuscript sha256 95994d2d…), Lemma 2.1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_ParityCubes_cubeSum
import Definitions.Def_ParityCubes_anfCoeff

set_option autoImplicit false

namespace ParityCubes

/-- **Lemma 2.1 (maximal-term rule)** (Sheshadri–Smirnov, arXiv:2611.00289, manuscript sha256
95994d2d…, Lemma 2.1, p.3 (PDF p.4), after Smirnov [Smi26]). `D_S f = Σ_{A ⊇ S} c_A x_{A∖S}` for every
`S` and every point `y`. For nonempty `S`, `D_S f ≡ 1` iff `S` is a maximal support of `f`, and
`D_S f ≡ 0` iff no support of `f` contains `S`.

**Formalization Note.** The sum over `𝔽₂` is the parity of the number of `A ⊇ S` with `c_A = 1` and
`y_i = 1` for all `i ∈ A ∖ S`. The first clause holds also for `S = ∅`, where `D_∅ f = f` and it says
that `anfCoeff` gives the algebraic normal form of `f`. -/
theorem lemma_2_1 {α : Type*} [Fintype α] [DecidableEq α] (f : (α → Bool) → Bool) :
    (∀ (S : Finset α) (y : α → Bool),
      cubeSum f S y = decide (Odd (Finset.univ.filter (fun A : Finset α =>
        S ⊆ A ∧ anfCoeff f A = true ∧ ∀ i ∈ A \ S, y i = true)).card)) ∧
    (∀ S : Finset α, S.Nonempty →
      ((∀ y : α → Bool, cubeSum f S y = true) ↔ IsMaxSupport f S) ∧
      ((∀ y : α → Bool, cubeSum f S y = false) ↔ ∀ A : Finset α, S ⊆ A → ¬ IsSupport f A)) := by sorry

end ParityCubes
