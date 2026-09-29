-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar
-- name    : WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/41c68ba2-11b2-532c-850e-d20779897e57
-- title:
--   Nonzero ℓ-torsion in the zero component at multiplicative reduction, ℓ≠ q
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$ (given by coefficients $a_1,\dots,a_6\in\mathbb Z$), let $q$ be a prime number, and assume $W.\Delta\neq 0$, $q\mid W.\Delta$ and $q\nmid W.c_4$ in $\mathbb Z$. Let $A$ be a valuation subring of $\operatorname{AlgebraicClosure}\mathbb Q$ satisfying the project's predicate [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), which unfolds to: the image of $q$ in $\operatorname{AlgebraicClosure}\mathbb Q$ is a non-unit of $A$ (so $A$ is a place of $\overline{\mathbb Q}$ of residue characteristic $q$). Let $\ell$ be a prime number with $\ell\neq q$. The conclusion asserts the existence of an element $P$ of the $\mathbb Z$-submodule `Submodule.torsionBy ℤ … ℓ` of the group of affine points of the base change of $W$ to $\operatorname{AlgebraicClosure}\mathbb Q$ (that is, a point killed by $\ell$) such that $P\neq 0$ and the underlying point lies in `W.InZeroComponentAt A`. The latter is the project's own notion, defined to mean: the point is $0$, or it is $\mathrm{some}\,x\,y$ with either $x\notin A$, or $x,y\in A$ and the pair of residues of $x,y$ in the residue field $\operatorname{ResidueField} A$ is a nonsingular point of the Weierstrass curve obtained from $W$ by reducing its integral coefficients into that residue field. Since $P\neq 0$, the conclusion says that this second, non-trivial disjunct holds for some nonzero $\ell$-torsion point. Note that nothing more than membership in the $\ell$-torsion is claimed; for $\ell$ prime and $P\neq 0$ this is exact order $\ell$.
--
--   Classically this is the statement that at a place of multiplicative reduction the zero component meets the $\ell$-torsion nontrivially, $E^0\cap E[\ell]\neq 0$, which for the Tate parametrisation follows from $\mu_\ell\subset E^0[\ell]$. The formal statement differs from the textbook one in being about a fixed integral Weierstrass model $W$ over $\mathbb Z$ with $q\mid\Delta$, $q\nmid c_4$ (no minimality or semistability hypothesis elsewhere), about an arbitrary valuation subring $A$ of $\overline{\mathbb Q}$ in which $q$ is a non-unit, and in using the project's explicit reduction-theoretic predicate `InZeroComponentAt` in place of the component group of a Néron model. It is the case $\ell\neq q$ of [`WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_multiplicativeReduction`](thm.html#WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_multiplicativeReduction), and is used through that result in the proof that the mod-$p$ representation of a Frey curve has no Galois-stable cofixed line for $p\geq 17$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar.lean

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

theorem WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_ne_residueChar
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) :
    ∃ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ, P ≠ 0 ∧ W.InZeroComponentAt A (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by sorry
