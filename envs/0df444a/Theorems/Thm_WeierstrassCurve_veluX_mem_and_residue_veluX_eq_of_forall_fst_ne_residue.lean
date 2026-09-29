-- Prove2me | Theorems.Thm_WeierstrassCurve_veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue
-- name    : WeierstrassCurve.veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/0f87d116-ae4b-50d7-b228-5ecddac37f1d
-- title:
--   Reduction commutes with Vélu's abscissa map off the kernel
-- statement:
--   Let $L$ be a field with decidable equality, $A \subseteq L$ a valuation subring whose residue field `IsLocalRing.ResidueField A` also carries decidable equality, and let $E$ be a Weierstrass curve over $A$ whose reduction $E \bmod \mathfrak m$, i.e. the base change `E.map (IsLocalRing.residue A)`, has nonvanishing discriminant $\Delta \neq 0$ (hypothesis `hΔ`). Let $n$ be a natural number such that the image of $2n+1$ in the residue field is nonzero, and let $Q$ be an affine point of the base change `E.map A.subtype` to $L$ with $\mathrm{addOrderOf}\,Q = 2n+1$, whose image [`WeierstrassCurve.reduceHom hΔ Q`](def/WeierstrassCurve_ReduceHom.html#L481) under reduction (the additive map sending $0$ to $0$ and a point $(x,y)$ to the pair of residues of $x$ and $y$ when $x \in A$, and to $0$ otherwise) again has additive order $2n+1$. Let $x \in L$ lie in $A$, and assume that for every pair $P$ in the odd-order summing set of the reduced curve for the reduced point, namely the image of $\{1,\dots,n\}$ under $k \mapsto$ the coordinate pair of $k \cdot \overline{Q}$ (with the point at infinity recorded as $(0,0)$), the first coordinate $P.1$ differs from the residue of $x$. Then the value $$\mathrm{veluX}(x) = x + \sum_{P \in S}\Bigl(\frac{t_P}{x - P.1} + \frac{u_P}{(x - P.1)^2}\Bigr),\qquad t_P = 2\,\mathrm{veluGx}(P) - a_1\,\mathrm{veluGy}(P),\quad u_P = \mathrm{veluGy}(P)^2,$$ formed over the analogous summing set $S$ of $E.map A.subtype$ for $Q$, lies in $A$, and its residue equals the corresponding Vélu abscissa value of the reduced curve, formed over the reduced summing set and evaluated at the residue of $x$; the conclusion is phrased as an existential over the membership proof, with the residue taken of $x$ paired with that proof.
--
--   This is the pointwise compatibility, on abscissae, of Vélu's formulae for the quotient by a cyclic subgroup of odd order $2n+1$ with reduction modulo the maximal ideal of a valuation subring, under the assumption that the evaluation point does not reduce onto the abscissa of a nontrivial kernel point. It is used to compare Vélu quotients over $L$ with Vélu quotients over the residue field, in particular by [`WeierstrassCurve.residue_cyclicQuotientJ_eq_cyclicQuotientJ_map_reduceHom`](thm.html#WeierstrassCurve.residue_cyclicQuotientJ_eq_cyclicQuotientJ_map_reduceHom) and by the two lifting statements [`WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples`](thm.html#WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples) and [`WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero`](thm.html#WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
    [DecidableEq (IsLocalRing.ResidueField A)]
    {E : WeierstrassCurve A} (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) {n : ℕ}
    (hm : ((2 * n + 1 : ℕ) : IsLocalRing.ResidueField A) ≠ 0)
    (Q : (E.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hQ' : addOrderOf (WeierstrassCurve.reduceHom hΔ Q) = 2 * n + 1)
    {x : L} (hx : x ∈ A)
    (hx' : ∀ P ∈ (E.map (IsLocalRing.residue A)).oddOrderSummingSet
      (WeierstrassCurve.reduceHom hΔ Q) n, P.1 ≠ IsLocalRing.residue A ⟨x, hx⟩) :
    ∃ hmem : (E.map A.subtype).veluX ((E.map A.subtype).oddOrderSummingSet Q n) x ∈ A,
      IsLocalRing.residue A ⟨_, hmem⟩ =
        (E.map (IsLocalRing.residue A)).veluX
          ((E.map (IsLocalRing.residue A)).oddOrderSummingSet (WeierstrassCurve.reduceHom hΔ Q) n)
          (IsLocalRing.residue A ⟨x, hx⟩) := by sorry
