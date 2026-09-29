-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_injective_localFlatClassesAd_selfExt_of_hondaSystem_model
-- name    : ResidualGaloisRep.exists_injective_localFlatClassesAd_selfExt_of_hondaSystem_model
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/16c2ec14-ea4e-58f6-925d-36e7c9e227df
-- title:
--   Local flat classes inject into Honda self-extensions
-- statement:
--   Let $k$ be a finite field of characteristic $p$ with $p\neq 2$, let $\mathbb{Z}_p\to\mathbb{Z}/p$ be an algebra structure whose kernel is $(p)$, and let $\bar\rho$ consist of a two-dimensional $k$-space $V$ together with a homomorphism $\rho$ from $\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{End}_k V$ factoring through a finite extension of $\mathbb{Q}$. Assume: (i) there is a commutative $\mathbb{Z}_p$-Hopf algebra $H$, finite flat and cocommutative over $\mathbb{Z}_p$, with $\mathrm{Hom}_{\mathbb{Z}/p\text{-lin}}(\mathbb{Z}/p\otimes_{\mathbb{Z}_p}H,\mathbb{Z}/p)$ a local ring, and a bijection $e$ from the convolution monoid of $\mathbb{Z}_p$-algebra maps $H\to\overline{\mathbb{Q}_p}$ onto $V\times V$ carrying convolution to addition and the action of $\mathrm{Aut}_{\mathbb{Q}_p}(\overline{\mathbb{Q}_p})$ on points to the diagonal action $\sigma\cdot(x_1,x_2)=(\rho(\sigma)x_1,\rho(\sigma)x_2)$ attached to the zero cocycle; (ii) a second such Hopf algebra $H_1$, free of rank $(\#k)^2$, with the analogous local Cartier dual and with a convolution-additive, Galois-equivariant bijection $e_1$ from its $\overline{\mathbb{Q}_p}$-points onto $V$; (iii) a map $\theta$ from $k$ to bialgebra endomorphisms of $H_1$ inducing the $k$-scalars through $e_1$, multiplicative, unital, and additive for convolution. Let $D$ be a finite-dimensional $k$-space with $\dim_k D=2$ and $\mathcal{H}$ a Honda system over $k$ for $\ell=0$ (so $F\circ V=V\circ F=0$, with submodule $L$ satisfying the Honda axioms), and let $\iota$ be an additive isomorphism of $D$ with the Dieudonné module of $\mathbb{Z}/p\otimes_{\mathbb{Z}_p}H_1$ matching $\mathcal{H}.F$, $\mathcal{H}.V$ with Frobenius and Verschiebung, $L$ with the Fontaine–Hodge submodule attached to $H_1\to\mathbb{Z}/p\otimes_{\mathbb{Z}_p}H_1$, and the $k$-action with the maps induced by $\theta$. Then there exists an injective $k$-linear map from the subspace of $H^1$ of the local Galois group with coefficients in $\mathrm{ad}\,\bar\rho$ spanned by classes of cocycles $c$ admitting such a finite flat cocommutative Hopf-algebra model of the extension $V\times V$ with action twisted by $c$, into $\mathcal{H}$'s self-extension module, the pairs $(X,Y)$ of endomorphisms of $D$ with $F\circ Y+X\circ V=0$ and $V\circ X+Y\circ F=0$ modulo the inner pairs.
--
--   This is the Fontaine–Conrad comparison between the flat local condition at $p$ on $H^1(\mathbb{Q}_p,\mathrm{ad}\,\bar\rho)$ and extension data for the Honda system of the finite flat model, in the form of the inequality $\dim_k H^1_f\le\dim_k\mathrm{selfExt}(\mathcal{H})$. It feeds the computation bounding the dimension of the flat local condition used in the Selmer-group estimates of the modularity lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_injective_localFlatClassesAd_selfExt_of_hondaSystem_model.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_HondaSelfExt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped PadicInt TensorProduct

theorem ResidualGaloisRep.exists_injective_localFlatClassesAd_selfExt_of_hondaSystem_model
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (hunip : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f))
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : Module.finrank ℤ_[p] H₁ = Nat.card k ^ 2)
    (hunip₁ : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H₁)))
    (e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H₁, g h = ResidualGaloisRep.localAut p σ (f h)) →
        e₁ g = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (e₁ f))
    (θ : k → (H₁ →ₐc[ℤ_[p]] H₁))
    (hθ : ∀ (a : k) (f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
      e₁ (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H₁ →ₐ[ℤ_[p]] H₁))) = a • e₁ f)
    (hθ_mul : ∀ a b : k, θ (a * b) = (θ a).comp (θ b)) (hθ_one : θ 1 = BialgHom.id ℤ_[p] H₁)
    (hθ_add : ∀ a b : k, WithConv.toConv (θ (a + b) : H₁ →ₐ[ℤ_[p]] H₁) =
      WithConv.toConv (θ a : H₁ →ₐ[ℤ_[p]] H₁) * WithConv.toConv (θ b : H₁ →ₐ[ℤ_[p]] H₁))
    (hθ_zero : WithConv.toConv (θ 0 : H₁ →ₐ[ℤ_[p]] H₁) = 1)
    (D : Type) [AddCommGroup D] [Module k D] [FiniteDimensional k D] (𝓗 : Deformation.HondaSystem (0 : k) D)
    (ι : D ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁))
    (hιF : ∀ x, ι (𝓗.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιV : ∀ x, ι (𝓗.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H₁) (ι x))
    (hιL : ∀ x, x ∈ 𝓗.L ↔ ι x ∈ Deformation.fontaineHodge (ZMod p) p
      (Algebra.TensorProduct.includeRight : H₁ →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H₁).toRingHom)
    (hιsmul : ∀ (a : k) (x : D), ι (a • x) = Deformation.DieudonneModule.map (ZMod p) p
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θ a)) (ι x))
    (hD : Module.finrank k D = 2) :
    ∃ f : ρbar.localFlatClassesAd p →ₗ[k] 𝓗.selfExt, Function.Injective f := by sorry
