-- Prove2me | Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isOdd
-- name    : WeierstrassCurve.residualGaloisRepOf_isOdd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/d4ea1286-fdf5-5f9e-96b2-9c4757075988
-- title:
--   Oddness of the mod-p representation of an elliptic curve
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Q}$ which is elliptic (the typeclass `W.IsElliptic`), and let $p$ be a natural number carrying the instance `Fact p.Prime`. Assume two hypotheses, which are exactly the data required to build the project's residual representation attached to $W$ at $p$: first, `hcard`, that the group of $p$-torsion points of $W$ base-changed to `AlgebraicClosure ℚ`, realised as the submodule `Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p`, has cardinality exactly $p^{2}$; second, `hker`, that the monoid homomorphism [`WeierstrassCurve.Affine.Point.galoisRepModuleEnd ℚ W p`](def/EllipticCurve_FrobeniusTrace.html#L25), i.e. the action of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ on this $p$-torsion module by $\mathbb{Z}/p$-linear endomorphisms, satisfies [`GaloisFactorsThroughFiniteLevel`](def/GaloisRep_Residual.html#L17): there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every automorphism fixing $L$ pointwise is sent to the identity. From these data the project forms `W.residualGaloisRepOf p hcard hker`, an object of type [`ResidualGaloisRep (ZMod p)`](def/GaloisRep_Residual.html#L22): the module $W[p](\overline{\mathbb{Q}})$ over $\mathbb{Z}/p$, of rank $2$, together with that Galois action. The conclusion is that this object satisfies the project's predicate [`ResidualGaloisRep.IsOdd`](def/GaloisRep_Residual.html#L57), which by definition says: for every $c \in \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ with $c \cdot c = 1$ and $c \neq 1$, the determinant of the $\mathbb{Z}/p$-linear endomorphism by which $c$ acts equals $-1$. Note that the quantification is over all non-trivial involutions of the absolute Galois group, not over a single chosen complex conjugation, and that the assertion is about the determinant alone, not about the full determinant character being the mod-$p$ cyclotomic character.
--
--   Classically this is the statement that $\bar\rho_{E,p}$ is odd, which follows from the identification of $\det\bar\rho_{E,p}$ with the mod-$p$ cyclotomic character via the Galois-equivariance of the Weil pairing (Darmon–Diamond–Taylor, §2.2; Silverman, Arithmetic of Elliptic Curves, Ch. III). The formal statement is packaged differently in two ways: it is expressed through the project's structure [`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22), so it presupposes the cardinality hypothesis `hcard` and the finite-level hypothesis `hker` used to construct that structure, and its `IsOdd` clause asks for determinant $-1$ at every non-trivial involution of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ rather than at a fixed complex conjugation. It is used downstream as the oddness input to the residual-modularity and level-lowering steps applied to the Frey curve, and in the construction of patching data in the Hecke-algebra arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_residualGaloisRepOf_isOdd.lean

import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.residualGaloisRepOf_isOdd (W : WeierstrassCurve ℚ) [W.IsElliptic] (p : ℕ) [Fact p.Prime] (hcard : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) (hker : GaloisFactorsThroughFiniteLevel (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p)) : (W.residualGaloisRepOf p hcard hker).IsOdd := by sorry
