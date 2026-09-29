-- Prove2me | Theorems.Thm_WeierstrassCurve_addOrderOf_reduceHom_of_natCast_ne_zero
-- name    : WeierstrassCurve.addOrderOf_reduceHom_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/c5282bab-49a0-54f3-8bc6-0eb9d911747d
-- title:
--   Reduction preserves the order of torsion prime to the residue characteristic
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, with residue field $\mathrm{ResidueField}\ A$ and residue map $\mathrm{residue}\ A$, and let $W$ be a Weierstrass curve over $A$. Assume the discriminant of the reduced curve $W.\mathrm{map}\ (\mathrm{residue}\ A)$ is nonzero, so that the reduction is a nonsingular Weierstrass curve over the residue field; this hypothesis $h\Delta$ is what makes the reduction map on points available. Let $N$ be a natural number whose image in $\mathrm{ResidueField}\ A$ is nonzero, and let $P$ be a point of the affine curve $W.\mathrm{map}\ A.\mathrm{subtype}$, that is of $W$ base changed to $L$ along the inclusion $A \hookrightarrow L$, whose additive order $\mathrm{addOrderOf}\ P$ equals $N$. Then the additive order of $\mathrm{reduceHom}\ h\Delta\ P$ is also $N$, where $\mathrm{reduceHom}\ h\Delta$ is the group homomorphism from the points of $W$ over $L$ to the points of the reduced curve that sends the point at infinity to the point at infinity, sends an affine point $(x,y)$ with $x \in A$ to the point with coordinates the residues of $x$ and $y$, and sends an affine point with $x \notin A$ to the point at infinity.
--
--   This is the classical assertion that reduction is order-preserving on torsion of order invertible in the residue field (Silverman, Proposition VII.3.1(b)), here for a Weierstrass model over an arbitrary valuation subring with nonsingular reduction. It is used to transport points of exact order $\ell$, and hence generators of cyclic $\ell$-subgroups and kernels of cyclic $\ell$-isogenies, between the generic and the special fibre; the citing statements concern Tate points and cyclic quotients in the analysis of modular curves at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_addOrderOf_reduceHom_of_natCast_ne_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve IsLocalRing

theorem WeierstrassCurve.addOrderOf_reduceHom_of_natCast_ne_zero
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {P : (W.map A.subtype).toAffine.Point} (hP : addOrderOf P = N) :
    addOrderOf (reduceHom hΔ P) = N := by sorry
