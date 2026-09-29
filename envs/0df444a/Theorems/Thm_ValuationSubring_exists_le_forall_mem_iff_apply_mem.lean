-- Prove2me | Theorems.Thm_ValuationSubring_exists_le_forall_mem_iff_apply_mem
-- name    : ValuationSubring.exists_le_forall_mem_iff_apply_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/c1abd654-fed3-53e4-932b-4fadccdc52f7
-- title:
--   Composite of a valuation ring with one of its residue field
-- statement:
--   Let $F$ be a field and $O \subseteq F$ a valuation subring, let $\bar K$ be a field and $\mathrm{res} : O \to \bar K$ a ring homomorphism whose kernel contains the maximal ideal of the local ring $O$, and let $W \subseteq \bar K$ be a valuation subring. The assertion is that there exists a valuation subring $O' \subseteq F$ with three properties: $O'$ is contained in $O$; for every $x \in O$ the image of $x$ in $F$ lies in $O'$ if and only if $\mathrm{res}(x) \in W$; and for every $x \in O$ the image of $x$ in $F$ lies in the non-units of $O'$ if and only if $\mathrm{res}(x)$ lies in the non-units of $W$ (here, for a valuation subring, membership in `nonunits` means being zero or having inverse outside the subring). No surjectivity of $\mathrm{res}$ is assumed, and $\bar K$ is not required to be the residue field of $O$; only that $\mathrm{res}$ kills the maximal ideal. Since $O' \le O$, the second condition pins $O'$ down as $\{x \in O : \mathrm{res}(x) \in W\}$.
--
--   This is the classical composition of a valuation of $F$ with a valuation of its residue field (a "place of a place"), which adds the rank of $W$ to that of $O$. It is used in the construction of places prolonging a given one, via [`AlgebraicCurve.RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits`](thm.html#AlgebraicCurve.RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits) and [`ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card`](thm.html#ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_le_forall_mem_iff_apply_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_le_forall_mem_iff_apply_mem
    {F : Type*} [Field F] (O : ValuationSubring F)
    {Kbar : Type*} [Field Kbar] (res : O →+* Kbar)
    (hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker res)
    (W : ValuationSubring Kbar) :
    ∃ O' : ValuationSubring F, O' ≤ O ∧
      (∀ x : O, (x : F) ∈ O' ↔ res x ∈ W) ∧
      (∀ x : O, (x : F) ∈ O'.nonunits ↔ res x ∈ W.nonunits) := by sorry
