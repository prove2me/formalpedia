-- Prove2me | Theorems.Thm_ResidualGaloisRep_isFlatAt_ofResidualGaloisRep_of_baseChangeAlong
-- name    : ResidualGaloisRep.isFlatAt_ofResidualGaloisRep_of_baseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/acb4e6ac-1ba6-54f4-960a-f982856e0a0d
-- title:
--   Flatness at p descends along an extension of coefficients
-- statement:
--   Let $k$ and $k'$ be fields, $\psi\colon k\to k'$ a ring homomorphism, $p$ a natural number, and $\rho$ a residual Galois representation over $k$, that is, a $k$-vector space $V$ with $\dim_k V=2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (realised as the $\mathbb Q$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb Q$) to $\mathrm{End}_k V$ which factors through a finite level: some intermediate field $L$ with $\mathbb Q\subseteq L\subseteq\overline{\mathbb Q}$ finite over $\mathbb Q$ has the property that every $\sigma$ fixing $L$ pointwise acts as the identity. Regard $\rho$ and its base change $k'\otimes_k V$ along $\psi$ (with the induced semilinear Galois action) as adic Galois representations over the local rings $k$, $k'$ via [`GaloisRepAdic.ofResidualGaloisRep`](def/GaloisRep_Adic.html#L196). Assume the base-changed representation is flat at $p$, i.e. the residue field $k'$ is finite and, for every ideal $I'$ of $k'$ with $k'/I'$ finite, there is a commutative, cocommutative Hopf algebra $H$ over the subring $\mathrm{ratLocalizedAt}\ p$ of $\mathbb Q$ consisting of the rationals whose denominator is coprime to $p$, module-finite and flat over that subring, and a bijection between the $\overline{\mathbb Q}$-points $\mathrm{Hom}_{\mathrm{alg}}(H,\overline{\mathbb Q})$ (with the convolution group law) and $(k'\otimes_k V)/I'\cdot(k'\otimes_k V)$ carrying the group law to addition and the pointwise Galois action on points to the induced action of $\sigma$ on the quotient. Then $\rho$ itself is flat at $p$ in the same sense: $k$ is finite and each quotient $V/I\cdot V$, for $I$ an ideal of $k$ with $k/I$ finite, is so realised.
--
--   This is the descent of the finite-flatness condition at $p$ for a two-dimensional residual representation through an extension of the coefficient field, the underlying geometric input being that Galois submodules of points of finite flat commutative group schemes over $\mathbb Z_{(p)}$ are again of this form. It is used to transfer non-flatness of a residual representation over $k$ to its base change, in the Hecke-algebra arguments deducing strict ordinarity at $p$ from failure of flatness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_isFlatAt_ofResidualGaloisRep_of_baseChangeAlong.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ResidualGaloisRep.isFlatAt_ofResidualGaloisRep_of_baseChangeAlong
    {k k' : Type} [Field k] [Field k'] (ψ : k →+* k') (ρ : ResidualGaloisRep k) {p : ℕ}
    (h : (GaloisRepAdic.ofResidualGaloisRep (ρ.baseChangeAlong ψ)).IsFlatAt p) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsFlatAt p := by sorry
