-- Prove2me | Theorems.Thm_PowerSeries_exists_eq_C_mul_map_of_mem_span_of_saturated
-- name    : PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/0f3c72ea-08dc-5c81-bb6c-e5ec179170b1
-- title:
--   Reduction of a saturated lattice of integral power series
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, with maximal ideal giving residue field $k =$ `IsLocalRing.ResidueField A` and reduction homomorphism `IsLocalRing.residue A : A → k`. Let $N$ be an additive subgroup of $\mathbb{Z}[[q]]$ which is saturated in the sense that for every integer $n \neq 0$ and every $p \in \mathbb{Z}[[q]]$, if $n \cdot p \in N$ then $p \in N$. Let $V \in L[[q]]$ lie in the $L$-submodule of $L[[q]]$ spanned by the set of coefficientwise images $p \mapsto$ `p.map (Int.castRingHom L)` of the elements $p \in N$, and suppose $V \neq 0$. Then there are a scalar $c \in L$ and a power series $u \in A[[q]]$ with: $c \neq 0$; $V = C(c) \cdot u_L$, where $u_L \in L[[q]]$ is obtained from $u$ by applying the inclusion $A \hookrightarrow L$ to each coefficient; the coefficientwise reduction $\bar{u} \in k[[q]]$ of $u$ is nonzero; and $\bar{u}$ lies in the $k$-submodule of $k[[q]]$ spanned by the coefficientwise images of the elements of $N$ under $\mathbb{Z} \to k$.
--
--   This is the statement that a saturated lattice $N$ of integral power series behaves well under reduction along a valuation ring: after scaling away the denominators of a nonzero $L$-combination one obtains an $A$-integral series whose reduction is again nonzero and again a $k$-combination of reductions of elements of $N$. It is used in the analysis of $q$-expansions over the function field of a modular curve, where a $q$-expansion is normalised to be integral at a place and then reduced, as in [`ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL`](thm.html#ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL) and the prolongation statements for Laurent base changes of function-field $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_exists_eq_C_mul_map_of_mem_span_of_saturated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated
    {L : Type*} [Field L] (A : ValuationSubring L)
    (N : AddSubgroup (PowerSeries ℤ))
    (hN : ∀ (n : ℤ) (p : PowerSeries ℤ), n ≠ 0 → n • p ∈ N → p ∈ N)
    {V : PowerSeries L}
    (hV : V ∈ Submodule.span L
      ((fun p : PowerSeries ℤ => p.map (Int.castRingHom L)) '' (N : Set (PowerSeries ℤ))))
    (hV0 : V ≠ 0) :
    ∃ (c : L) (u : PowerSeries A), c ≠ 0 ∧
      V = PowerSeries.C c * u.map (A.subtype : A →+* L) ∧
      u.map (IsLocalRing.residue A) ≠ 0 ∧
      u.map (IsLocalRing.residue A) ∈
        Submodule.span (IsLocalRing.ResidueField A)
          ((fun p : PowerSeries ℤ => p.map (Int.castRingHom (IsLocalRing.ResidueField A))) ''
            (N : Set (PowerSeries ℤ))) := by sorry
