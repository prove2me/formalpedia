-- Prove2me | Theorems.Thm_WeierstrassCurve_finrank_torsionBy_of_isAlgClosed
-- name    : WeierstrassCurve.finrank_torsionBy_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/42a5a9fe-3c16-5257-9cc3-52663ecfc01e
-- title:
--   Mod-p torsion of an elliptic curve has 𝔽ₚ-dimension 2
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra and $K$ algebraically closed, let $W$ be a Weierstrass curve over $F$ whose discriminant is invertible (`W.IsElliptic`), and let $p$ be a prime number. Write $(W⁄K)$ for the base change of $W$ to $K$ and $(W⁄K)$`.Point` for its group of $K$-points (the affine points of the Weierstrass equation together with the point at infinity), regarded as a $\mathbb{Z}$-module. Assume that $p$ is nonzero in $K$, i.e. the image of $p$ under $\mathbb{N}\to K$ does not vanish, which for a field of characteristic $\ell$ means $p \neq \ell$. Then the $p$-torsion submodule `Submodule.torsionBy ℤ (W⁄K).Point p`, consisting of those $K$-points killed by $p$ and carrying the $\mathbb{Z}/p\mathbb{Z}$-module structure supplied by the project's definitions, has finite rank $2$ over $\mathbb{Z}/p\mathbb{Z}$: $$\operatorname{finrank}_{\mathbb{Z}/p\mathbb{Z}} E[p](K) = 2 .$$ Thus the conclusion is the dimension count, not the isomorphism $E[p] \cong (\mathbb{Z}/p\mathbb{Z})^2$ itself.
--
--   This is the standard structure result for the $p$-torsion of an elliptic curve over an algebraically closed field of characteristic different from $p$, recorded in the shape needed to treat $E[p](\overline{F})$ as a two-dimensional $\mathbb{F}_p$-vector space. It is what makes the mod-$p$ representation attached to an elliptic curve two-dimensional, and it is used downstream in the construction of the residual representations and in the congruence and level statements about modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_finrank_torsionBy_of_isAlgClosed.lean

import Mathlib.LinearAlgebra.Dimension.Finrank
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.finrank_torsionBy_of_isAlgClosed {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {p : ℕ} [Fact p.Prime] (hp : (p : K) ≠ 0) : Module.finrank (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p) = 2 := by sorry
