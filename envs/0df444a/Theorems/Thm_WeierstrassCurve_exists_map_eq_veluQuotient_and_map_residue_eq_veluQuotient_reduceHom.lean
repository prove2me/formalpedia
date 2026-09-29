-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom
-- name    : WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/1a3f8bdf-8e0b-502a-8307-cfe521f89314
-- title:
--   Integral model of a Vélu quotient compatible with reduction
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring with residue field $\mathrm{ResidueField}(A)$ and residue map $\mathrm{residue}\,A$, and let $W$ be a Weierstrass curve over $A$, i.e. a tuple of coefficients $a_1,a_2,a_3,a_4,a_6 \in A$. Assume the reduced curve $W.\mathrm{map}\,(\mathrm{residue}\,A)$ has nonzero discriminant $\Delta$. Let $\ell$ be a natural number whose image in the residue field is nonzero, let $Q$ be a point of the affine curve attached to the base change $W.\mathrm{map}\,A.\mathrm{subtype}$ over $L$ whose additive order is exactly $\ell$, and let $n < \ell$. The assertion is that there exists a Weierstrass curve $V$ over $A$ satisfying two identities of coefficient tuples. First, the base change of $V$ to $L$ equals the Vélu quotient of $W.\mathrm{map}\,A.\mathrm{subtype}$ taken over the summing set $\{(x(kQ), y(kQ)) : 1 \le k \le n\} \subseteq L \times L$ (a multiple equal to the point at infinity contributing $(0,0)$); here the Vélu quotient over a finite set $S$ of pairs keeps $a_1,a_2,a_3$, replaces $a_4$ by $a_4 - 5\sum_{P \in S} \mathrm{veluT}(P)$ and $a_6$ by $a_6 - b_2\sum_{P \in S}\mathrm{veluT}(P) - 7\sum_{P\in S}\mathrm{veluW}(P)$. Second, the reduction $V.\mathrm{map}\,(\mathrm{residue}\,A)$ equals the Vélu quotient of the reduced curve over the analogous summing set formed from the multiples of $\mathrm{reduceHom}\,h\Delta\,Q$, the image of $Q$ under the reduction homomorphism which sends an affine point with integral $x$-coordinate to the reduction of its coordinates and any other point to the origin.
--
--   This is the good-reduction bookkeeping for Vélu's isogeny formulae: when the order $\ell$ of the kernel generator is invertible in the residue field, the Vélu quotient of the generic fibre already has a Weierstrass model over the valuation ring, and its reduction is the Vélu quotient of the reduced curve by the reduced summing set. It is used to compare $j$-invariants of cyclic quotients with their reductions, and thereby in the factorisation of modular polynomial fibres into $j$-invariants of Vélu quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_ReduceHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve IsLocalRing

theorem WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom
    {L : Type*} [Field L] [DecidableEq L] (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = ℓ) {n : ℕ} (hn : n < ℓ) :
    ∃ V : WeierstrassCurve A,
      V.map A.subtype = (W.map A.subtype).veluQuotient ((W.map A.subtype).oddOrderSummingSet Q n) ∧
      V.map (residue A) =
        (W.map (residue A)).veluQuotient ((W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) n) := by sorry
