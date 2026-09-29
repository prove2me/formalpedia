-- Prove2me | Theorems.Thm_ResidualGaloisRep_finiteDimensional_localFlatClassesAd_and_finrank_le_of_isLocalRing_baseChange
-- name    : ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le_of_isLocalRing_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/d11c63da-c7fb-5dcc-b473-1c72c918e9b4
-- title:
--   Flat local bound for connected models of ad ρ̄
-- statement:
--   Let $k$ be a finite field, $p$ an odd prime with $\operatorname{char} k = p$, and fix an $\mathbb{Z}_p$-algebra structure on $\mathbb{Z}/p$ whose structure map has kernel the ideal $(p)$. Let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{End}_k V$ that is trivial on the automorphisms fixing some finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$. Assume (hypothesis `hconn`) that there is a commutative ring $H$ carrying a $\mathbb{Z}_p$-Hopf algebra structure, finite and flat as a $\mathbb{Z}_p$-module and cocommutative, such that $(\mathbb{Z}/p) \otimes_{\mathbb{Z}_p} H$ is a local ring, and a bijection $e$ from the set of $\mathbb{Z}_p$-algebra maps $H \to \overline{\mathbb{Q}}_p$, equipped with its convolution monoid structure, onto $V \times V$ which is additive, $e(f\ast g) = e f + e g$, and equivariant for the diagonal action: whenever $\sigma$ is a $\mathbb{Q}_p$-automorphism of $\overline{\mathbb{Q}}_p$ and $g = \sigma \circ f$ pointwise, then $e g = (\rho(\sigma)x_1, \rho(\sigma)x_2)$ for $e f = (x_1,x_2)$, $\sigma$ being mapped to the global Galois group by restriction; this is the $c = 0$ case of the twisted action `dualLiftModuleActAd`. The conclusion concerns the $k$-subspace $\bar\rho$`.localFlatClassesAd` $p$ of $H^1$ of the restriction along $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p) \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the adjoint representation $\sigma \mapsto (f \mapsto \rho(\sigma) f \rho(\sigma^{-1}))$ on $\mathrm{End}_k V$, namely the span of the classes of those $1$-cocycles $c$ for which some finite flat cocommutative $\mathbb{Z}_p$-Hopf algebra $H$ admits an additive bijection $e$ from its $\overline{\mathbb{Q}}_p$-points onto $V \times V$ intertwining the Galois action with the $c$-twisted action `dualLiftModuleActAd` $p$ $c$. It asserts that this subspace is finite-dimensional over $k$ and that its dimension is at most $1$ plus the $k$-dimension of the space of invariants of the restricted adjoint representation.
--
--   This is the local bound $\dim_k H^1_f(\mathbb{Q}_p, \mathrm{ad}\,\bar\rho) \le \dim_k H^0(\mathbb{Q}_p, \mathrm{ad}\,\bar\rho) + 1$ in the case where the given finite flat model has connected special fibre, the special fibre being connected here in the form that $(\mathbb{Z}/p)\otimes_{\mathbb{Z}_p} H$ is local. It feeds, together with the unipotent case, into the unconditional flat local bound [`ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le`](thm.html#ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le) used in the Selmer-group dimension count of the modularity lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_finiteDimensional_localFlatClassesAd_and_finrank_le_of_isLocalRing_baseChange.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.finiteDimensional_localFlatClassesAd_and_finrank_le_of_isLocalRing_baseChange
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (hconn : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (TensorProduct ℤ_[p] (ZMod p) H) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f)) :
    FiniteDimensional k (ρbar.localFlatClassesAd p) ∧
      Module.finrank k (ρbar.localFlatClassesAd p) ≤
        Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)).ρ.invariants + 1 := by sorry
