-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_reduceHom_apply_eq_zero
-- name    : WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_reduceHom_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/bc439620-800f-5855-ad30-b96acf66a9c0
-- title:
--   Reduction detects divisibility of rational homomorphisms by n
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and let $E_1, E_2$ be Weierstrass curves with coefficients in $A$ whose base changes $E_1 \otimes_A L$, $E_2 \otimes_A L$ along the inclusion $A \hookrightarrow L$ are elliptic (invertible discriminant). Assume the reduction $E_2 \otimes_A \kappa_A$ of $E_2$ along the residue map $A \to \kappa_A := \mathrm{ResidueField}(A)$ has discriminant $\Delta \neq 0$, and let $n$ be a natural number whose image in $\kappa_A$ is nonzero. Let $\gamma$ be an additive map from the group of affine points of $E_1 \otimes_A L$ to that of $E_2 \otimes_A L$ lying in `rationalHomSet`, i.e. $\gamma$ is either identically zero or rationally represented: there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ over $L$ and a finite set $B \subseteq L$ such that for every nonsingular affine point $(x,y)$ of the curve with $x \notin B$ one has $d_X(x,y) \neq 0 \neq d_Y(x,y)$ and $\gamma(x,y) = (n_X(x,y)/d_X(x,y),\, n_Y(x,y)/d_Y(x,y))$. Suppose that for every point $P$ with $nP = 0$ the point $\gamma(P)$ reduces to zero under `reduceHom`, the reduction homomorphism sending a point with integral $x$-coordinate to the residue of its coordinates and a point with non-integral $x$-coordinate to the origin. Then there exists $\delta$ in the same `rationalHomSet` with $\gamma(P) = n \cdot \delta(P)$ for all $P$.
--
--   This is the elementary ingredient in the statement that, at a place of good reduction, reduction of homomorphisms between elliptic curves has torsion-free cokernel away from the residue characteristic: divisibility by $n$ can be tested after reduction whenever $n$ is invertible in the residue field. It feeds into the construction of lifts of endomorphisms, being cited by [`WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul`](thm.html#WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_reduceHom_apply_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_reduceHom_apply_eq_zero {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (IsLocalRing.ResidueField A)] (E₁ E₂ : WeierstrassCurve A) [(E₁.map A.subtype).IsElliptic] [(E₂.map A.subtype).IsElliptic] (hΔ₂ : (E₂.map (IsLocalRing.residue A)).Δ ≠ 0) {n : ℕ} (hn : (n : IsLocalRing.ResidueField A) ≠ 0) {γ : (E₁.map A.subtype).toAffine.Point →+ (E₂.map A.subtype).toAffine.Point} (hγ : γ ∈ WeierstrassCurve.rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype)) (hker : ∀ P : (E₁.map A.subtype).toAffine.Point, (n : ℤ) • P = 0 → WeierstrassCurve.reduceHom hΔ₂ (γ P) = 0) : ∃ δ ∈ WeierstrassCurve.rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype), ∀ P : (E₁.map A.subtype).toAffine.Point, γ P = (n : ℤ) • δ P := by sorry
