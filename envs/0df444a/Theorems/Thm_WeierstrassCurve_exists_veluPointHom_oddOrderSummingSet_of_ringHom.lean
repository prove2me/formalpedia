-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_ringHom
-- name    : WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/4e2df712-9190-503e-b485-4e8c1d38c763
-- title:
--   Descent of the Vélu point homomorphism along a field homomorphism
-- statement:
--   Let $F$ and $L$ be fields, let $f\colon F \to L$ be a ring homomorphism, and let $W$ be an elliptic Weierstrass curve over $F$. Let $p$ be a natural number and let $Q$ be a point of the affine curve $W$ with $\mathrm{addOrderOf}\,Q = p$. For a curve $W'$ and a point $Q'$ on it write $S'$ for `W'.oddOrderSummingSet Q' (p / 2)`, the finite set of pairs in $L \times L$ obtained as the image of $k \mapsto$ (the coordinates of $k \cdot Q'$, with $(0,0)$ assigned to the point at infinity) for $k$ running over the integers from $1$ to $p/2$ (natural division), and write `W'.veluQuotient S'` for the curve with the same $a_1, a_2, a_3$ as $W'$ and with $a_4, a_6$ corrected by the Vélu sums $\sum_{P \in S'} t(P)$ and $\sum_{P \in S'} w(P)$. Assume, as hypothesis, that over $L$ the following holds for every elliptic curve $W'$ over $L$ and every point $Q'$ on it of additive order $p$: there is an additive map $\varphi'$ from $W'(L)$ to the points of `W'.veluQuotient S'` whose kernel is the subgroup of integer multiples of $Q'$ and which sends any nonsingular affine point $(x,y)$ not in that subgroup to the affine point with coordinates $(\mathtt{veluX}\,S'\,x, \mathtt{veluY}\,S'\,x\,y)$ (nonsingularity of the image being part of the assertion). The conclusion is the same statement for $W$ and $Q$ over $F$: with $S =$ `W.oddOrderSummingSet Q (p / 2)`, there is an additive map $\varphi$ from $W(F)$ to the points of `W.veluQuotient S` with kernel the integer multiples of $Q$, sending each nonsingular affine point $(x,y)$ outside that subgroup to the point with coordinates $(\mathtt{veluX}\,S\,x, \mathtt{veluY}\,S\,x\,y)$.
--
--   This is the descent step for the construction of the Vélu isogeny: the existence of the Vélu point homomorphism attached to a point of order $p$ transfers from a field $L$ receiving $F$ back to $F$ itself, so that taking $L$ an algebraic closure reduces the construction over an arbitrary field to the algebraically closed case. It is used by [`WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet`](thm.html#WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet) and, through it, by the construction of the quotient by a full kernel and the identification of the composite of two such quotients with multiplication.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_ringHom.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_ringHom
    {F L : Type*} [Field F] [DecidableEq F] [Field L] [DecidableEq L] (f : F →+* L)
    (W : WeierstrassCurve F) [W.IsElliptic]
    {p : ℕ} (Q : W.toAffine.Point) (hQord : addOrderOf Q = p)
    (hL : ∀ (W' : WeierstrassCurve L) [W'.IsElliptic] (Q' : W'.toAffine.Point), addOrderOf Q' = p →
      let S' := W'.oddOrderSummingSet Q' (p / 2)
      ∃ φ' : W'.toAffine.Point →+ (W'.veluQuotient S').toAffine.Point,
        φ'.ker = AddSubgroup.zmultiples Q' ∧
        (∀ (x y : L) (h : W'.toAffine.Nonsingular x y),
          (.some x y h : W'.toAffine.Point) ∉ AddSubgroup.zmultiples Q' →
            ∃ h', φ' (.some x y h) = .some (W'.veluX S' x) (W'.veluY S' x y) h')) :
    let S := W.oddOrderSummingSet Q (p / 2)
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient S).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (W.veluX S x) (W.veluY S x y) h') := by sorry
