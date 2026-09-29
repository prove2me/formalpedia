-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_fixedField_inertiaSubgroupIn_sub_mem_nonunits
-- name    : ValuationSubring.exists_mem_fixedField_inertiaSubgroupIn_sub_mem_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/75a21179-7d0a-52bd-b51e-274039ecd4fc
-- title:
--   Residues of a place of ℚ̄ come from its inertia field
-- statement:
--   Let $F$ be a number field equipped with an algebra structure over $\mathbb Q$-algebraic closure, i.e. a fixed embedding $F \subset \overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, let $P$ be a valuation subring of $\overline{\mathbb Q}$, and let $q$ be a prime number such that $P$ satisfies `LiesOverPrime q`, that is, the image of $q$ in $\overline{\mathbb Q}$ belongs to `P.nonunits` (the non-units of $P$, so that $q$ lies in the maximal ideal of $P$). Let $a$ be an element of $P$. The assertion is that there exists $c \in \overline{\mathbb Q}$ which lies in the fixed field of `P.inertiaSubgroupIn F` — the subgroup of $\overline{\mathbb Q} \simeq_{\mathrm{alg}[F]} \overline{\mathbb Q}$ obtained as the image of the inertia subgroup of $P$ over $F$ under the inclusion of the decomposition subgroup of $P$ over $F$ — such that $c \in P$ and, with the resulting membership $a - c \in P$, the element $a - c$ of $P$ lies in the maximal ideal of the local ring $P$. Thus every element of $P$ is congruent modulo $\mathfrak m_P$ to an element of $P$ lying in the inertia field of $P$ over $F$.
--
--   This is the surjectivity of the residue map of the inertia ring $P \cap \overline{\mathbb Q}^{\,I_F(P)}$ onto the residue field of $P$, in the concrete form 'each $a \in P$ is congruent mod $\mathfrak m_P$ to an element of the inertia field'. It supplies one of the properties of the constants used in [`ModularCurve.FullLevel.exists_valuationSubring_admissibleConstants_over_cyclotomic`](thm.html#ModularCurve.FullLevel.exists_valuationSubring_admissibleConstants_over_cyclotomic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_fixedField_inertiaSubgroupIn_sub_mem_nonunits.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_mem_fixedField_inertiaSubgroupIn_sub_mem_nonunits
    (F : Type) [Field F] [NumberField F] [Algebra F (AlgebraicClosure ℚ)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime] (hP : P.LiesOverPrime q)
    (a : AlgebraicClosure ℚ) (ha : a ∈ P) :
    ∃ c : AlgebraicClosure ℚ, c ∈ IntermediateField.fixedField (P.inertiaSubgroupIn F) ∧ c ∈ P ∧
      ∃ h : a - c ∈ P, (⟨a - c, h⟩ : ↥P) ∈ IsLocalRing.maximalIdeal ↥P := by sorry
