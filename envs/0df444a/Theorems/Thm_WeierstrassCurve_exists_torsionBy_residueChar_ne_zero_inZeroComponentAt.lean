-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_torsionBy_residueChar_ne_zero_inZeroComponentAt
-- name    : WeierstrassCurve.exists_torsionBy_residueChar_ne_zero_inZeroComponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/0cc300fe-d6a6-51a1-a1cb-a8013273f7d9
-- title:
--   Nonzero q-torsion in the zero component at residue characteristic q
-- statement:
--   Let $W$ be a Weierstrass equation over $\mathbb{Z}$ and $q$ a prime number. Assume $W$ has nonzero discriminant, $\Delta \neq 0$, that $q \mid \Delta$ and that $q \nmid c_4$ (multiplicative reduction at $q$). Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` such that $q$, viewed in $\overline{\mathbb{Q}}$, is a nonunit of $A$, i.e. $A$ lies over the prime $q$. Write $E$ for the base change to $\overline{\mathbb{Q}}$ of the Weierstrass curve obtained from $W$ by the ring map $\mathbb{Z} \to \mathbb{Q}$, and $E(\overline{\mathbb{Q}})$ for its group of points. The assertion is that the $\mathbb{Z}$-submodule of elements killed by $q$ in $E(\overline{\mathbb{Q}})$ contains an element $P$ with $P \neq 0$ whose underlying point satisfies `W.InZeroComponentAt A`: that is, either $P = 0$, or $P$ is an affine point $(x,y)$ with $x \notin A$, or $x, y \in A$ and the images of $x$ and $y$ in the residue field of $A$ are a nonsingular point of the Weierstrass curve obtained from $W$ by reduction to that residue field.
--
--   This is the residue-characteristic case ($\ell = q$) of the statement that a curve with multiplicative reduction at $q$ has nonzero $q$-torsion in the zero component at a place above $q$; classically it reflects the inclusion $\mu_q \subset E^0[q]$ for the Tate parametrisation $\overline{\mathbb{Q}}^\times / t^{\mathbb{Z}}$, the relevant points being those of the formal group, with non-integral abscissa. It feeds into [`WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_multiplicativeReduction`](thm.html#WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_multiplicativeReduction), whose remaining case $\ell \neq q$ is what the Fermat application uses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_torsionBy_residueChar_ne_zero_inZeroComponentAt.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_torsionBy_residueChar_ne_zero_inZeroComponentAt
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point q, P ≠ 0 ∧ W.InZeroComponentAt A (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by sorry
