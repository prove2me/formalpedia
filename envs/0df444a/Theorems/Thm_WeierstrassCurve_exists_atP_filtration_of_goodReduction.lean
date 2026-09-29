-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_atP_filtration_of_goodReduction
-- name    : WeierstrassCurve.exists_atP_filtration_of_goodReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/8a60cfce-0541-576d-96a5-ca021003035b
-- title:
--   Reduction-kernel filtration at a good ordinary prime p≠ 2
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and $p$ a prime (supplied as a `Fact`) with $p\neq 2$ and $p\nmid\Delta_W$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the project's sense `LiesOverPrime`, i.e. the image of $p$ in $\overline{\mathbb{Q}}$ lies in the nonunits of $A$. Assume an ordinarity hypothesis: there exist $x,y\in\overline{\mathbb{Q}}$ and a proof $h$ that $(x,y)$ is a nonsingular point of the affine curve obtained from $W$ by base change along $\mathbb{Z}\to\mathbb{Q}\to\overline{\mathbb{Q}}$, such that the corresponding point `Point.some x y h` is killed by $p$ and $x\in A$. Let $m\geq 1$. Then there is an additive subgroup $F$ of the group of $\overline{\mathbb{Q}}$-points of the base-changed curve with the following four properties. First, $F$ is characterised pointwise: a point $Q$ lies in $F$ if and only if $p^m\cdot Q=0$ and, for every affine presentation $Q=\,$`Point.some x y h`, the abscissa $x$ fails to lie in $A$ (so the point at infinity satisfies the second clause vacuously); thus $F$ is the intersection of the $p^m$-torsion with the kernel of reduction at $A$, described by the $x$-coordinate condition rather than via `InZeroComponentAt`. Second, $F$ is finite with exactly $p^m$ elements. Third, $F$ is stable under every $\sigma$ in the decomposition subgroup of $A$ over $\mathbb{Q}$, acting on points through $\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}}$. Fourth, $F$ absorbs inertial displacements of $p^m$-torsion: for every $\sigma$ in `A.inertiaSubgroupIn ℚ` (the image in the full Galois group of the inertia subgroup of $A$) and every point $y$ with $p^m\cdot y=0$, one has $\sigma\cdot y-y\in F$.
--
--   This is the finite-level form of the filtration used in Mazur's analysis of the local behaviour at $p$ of the mod $p$ (and mod $p^m$) representation of an elliptic curve with good ordinary reduction: the kernel of reduction meets $E[p^m]$ in a cyclic group of order exactly $p^m$, stable under the decomposition group and containing all inertial differences $\sigma y-y$. Compared with the textbook statement via formal groups of height one, the hypothesis of ordinarity is encoded concretely as the existence of an affine $p$-torsion point whose abscissa is $A$-integral, and the kernel of reduction is described by the condition that the abscissa not lie in $A$; the hypothesis $p\neq 2$ is genuinely used. The statement feeds the proof that the Frey curve admits no Galois-stable cofixed line in its $p$-torsion for $p\geq 17$ ([`FreyPackage.frey_no_cofixed_large`](thm.html#FreyPackage.frey_no_cofixed_large)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_atP_filtration_of_goodReduction.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
open WeierstrassCurve

theorem WeierstrassCurve.exists_atP_filtration_of_goodReduction
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpΔ : ¬ (p : ℤ) ∣ W.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hord : ∃ (x y : AlgebraicClosure ℚ)
      (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
      p • (Point.some x y h) = 0 ∧ x ∈ A)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ F : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      (∀ Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        Q ∈ F ↔ p ^ m • Q = 0 ∧
          ∀ (x y : AlgebraicClosure ℚ)
            (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
          Q = Point.some x y h → x ∉ A) ∧
      Nat.card F = p ^ m ∧
      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ F, σ • x ∈ F) ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        p ^ m • y = 0 → σ • y - y ∈ F := by sorry
