-- Prove2me | Theorems.Thm_WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero
-- name    : WeierstrassCurve.eq_of_reduceHom_eq_of_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/8a80e63f-063d-52ca-a1de-e5868101b3b6
-- title:
--   Reduction is injective on N-torsion when N is invertible
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, with residue field $\mathrm{ResidueField}\ A$ and reduction map $\mathrm{residue}\ A : A \to \mathrm{ResidueField}\ A$, and let $W$ be a Weierstrass curve over $A$. Assume that the discriminant of the reduced curve $W$ pushed forward along $\mathrm{residue}\ A$ is non-zero, so that the reduction is nonsingular. Let $N$ be a natural number whose image in the residue field is non-zero. Let $P$ and $Q$ be points of the affine curve obtained from $W$ by base change along the inclusion $A \hookrightarrow L$, i.e. points of the Weierstrass curve over $L$, and suppose $N \bullet P = 0$ and $N \bullet Q = 0$ in the group of points. Suppose further that $P$ and $Q$ have the same image under the additive homomorphism `reduceHom`, which sends the point at infinity to the point at infinity, sends an affine point $(x,y)$ with $x \in A$ to the point with coordinates the residues of $x$ and $y$, and sends an affine point whose $x$-coordinate does not lie in $A$ to the point at infinity. Then $P = Q$.
--
--   This is the injectivity of reduction on $N$-torsion for a Weierstrass model with nonsingular reduction over a valuation ring, when $N$ is invertible in the residue field (Silverman, VII.3.1(b)), here over an arbitrary, not necessarily discrete, valuation subring. It is used downstream to compare torsion subgroups and orders of torsion points before and after reduction, for instance in showing that `reduceHom` restricts to a bijection on $N$-torsion and that the order of a torsion point is preserved.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve IsLocalRing

theorem WeierstrassCurve.eq_of_reduceHom_eq_of_nsmul_eq_zero
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {P Q : (W.map A.subtype).toAffine.Point} (hP : N • P = 0) (hQ : N • Q = 0)
    (h : reduceHom hΔ P = reduceHom hΔ Q) : P = Q := by sorry
