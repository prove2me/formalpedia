-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_isLocallyFlatCocycleAd_smul_one
-- name    : ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/0df06240-cf85-5267-b477-6d3eee6523f8
-- title:
--   A non-zero locally flat scalar cocycle for ad ρ̄
-- statement:
--   Let $k$ be a field, $p$ a prime, and $\bar\rho$ a residual Galois representation over $k$, i.e. a two-dimensional $k$-vector space $V$ together with a monoid homomorphism $\bar\rho\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to \mathrm{End}_k V$ that is trivial on the elements fixing some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$. Write $G_p$ for `primeLocalGaloisGroup (pPrime p)`, the group of $\mathbb Q_p$-algebra automorphisms of `PadicAlgCl p`, mapped to the global group by restriction along `primeLocalToGlobal`. Assume `IsLocallyFlatCocycleAd p 0` holds for $\bar\rho$: there is a commutative cocommutative Hopf algebra $H$ over $\mathbb Z_p$, finite and flat as a $\mathbb Z_p$-module, and a bijection $e$ from the set of $\mathbb Z_p$-algebra homomorphisms $H\to$ `PadicAlgCl p`, with its convolution product, onto $V\times V$, which is additive ($e(fg)=e(f)+e(g)$) and satisfies $e(g)=(\bar\rho(\sigma)x_1,\ \bar\rho(\sigma)x_2)$ for $e(f)=(x_1,x_2)$ whenever $g=\sigma\circ f$, $\sigma\in G_p$. The conclusion: there exist a function $a\colon G_p\to k$ and a $1$-cocycle $c$ of $G_p$ acting on $\mathrm{End}_k V$ through the adjoint representation $\mathrm{ad}\,\bar\rho$ ($\sigma\colon f\mapsto \bar\rho(\sigma)f\bar\rho(\sigma)^{-1}$), restricted along `primeLocalToGlobal`, such that $c(\sigma)=a(\sigma)\cdot 1_V$ for all $\sigma$, $a(\sigma)\neq 0$ for at least one $\sigma$, and `IsLocallyFlatCocycleAd p c` holds, i.e. the same finite flat Hopf-algebraic description is available for $V\times V$ equipped with the twisted action $\sigma\cdot(v,w)=(\bar\rho(\sigma)v,\ c(\sigma)\bar\rho(\sigma)v+\bar\rho(\sigma)w)$. No additivity of $a$ in $\sigma$ is asserted.
--
--   This supplies the extra unramified scalar twist behind the inequality $\dim H^1_f(\mathbb Q_p,\mathrm{ad}^0\bar\rho)+1\le \dim H^1_f(\mathbb Q_p,\mathrm{ad}\,\bar\rho)$ in the local flat deformation theory at $p$. It is used by [`ResidualGaloisRep.finrank_localFlatClasses_add_one_le_finrank_localFlatClassesAd`](thm.html#ResidualGaloisRep.finrank_localFlatClasses_add_one_le_finrank_localFlatClassesAd), the dimension count in that inequality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_isLocallyFlatCocycleAd_smul_one.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (hflat : ρbar.IsLocallyFlatCocycleAd p 0) :
    ∃ (a : primeLocalGaloisGroup (pPrime p) → k)
      (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))),
      (∀ σ, (c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ =
          a σ • (1 : Module.End k ρbar.V)) ∧
        (∃ σ, a σ ≠ 0) ∧ ρbar.IsLocallyFlatCocycleAd p c := by sorry
