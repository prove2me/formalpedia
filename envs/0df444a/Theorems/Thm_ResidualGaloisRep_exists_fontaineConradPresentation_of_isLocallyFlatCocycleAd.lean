-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_fontaineConradPresentation_of_isLocallyFlatCocycleAd
-- name    : ResidualGaloisRep.exists_fontaineConradPresentation_of_isLocallyFlatCocycleAd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/4c383fae-fef2-599c-8e71-4b678a5ecc5a
-- title:
--   Fontaine–Conrad presentation of a locally flat ad-cocycle
-- statement:
--   Let $k$ be a finite field of characteristic $p$ with $p\neq 2$, let $\mathbb{Z}_p$ act on $\mathbb{Z}/p$ by an algebra map whose kernel is the ideal $(p)$, and let $\bar\rho$ be a residual representation, i.e. a two-dimensional $k$-space $\bar V$ together with a homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_k(\bar V)$ factoring through a finite level. Assume: (a) `hunip`, that $\bar V\oplus\bar V$ with the diagonal action `dualLiftModuleActAd p 0` is realised, additively and equivariantly for the local group at $p$ acting through `primeLocalToGlobal`, by the $\mathbb{Z}_p$-algebra homomorphisms of a finite flat cocommutative Hopf $\mathbb{Z}_p$-algebra into `PadicAlgCl p` under convolution, the Cartier dual of whose reduction mod $p$ is a local ring; (b) a finite free cocommutative Hopf algebra $H_1$ over $\mathbb{Z}_p$ of rank $|k|^2$, with local Cartier dual of its reduction, a bijection $e_1$ from its convolution monoid of points onto $\bar V$ carrying convolution to addition and intertwining the Galois actions, and a map $\theta\colon k\to\mathrm{End}_{\mathrm{bialg}}(H_1)$ which induces the $k$-scalars on $\bar V$ through $e_1$ and is multiplicative, unital, convolution-additive and convolution-trivial at $0$; (c) a finite-dimensional $k$-space $D$ with $\dim_k D=2$ carrying a Honda system $\mathcal H$ with parameter $0$ (so $FV=VF=0$, $\mathrm{range}\,F\sqcup L=D$, $V$ injective on $L$) and an additive isomorphism $\iota$ of $D$ with the Dieudonné module of $(\mathbb{Z}/p)\otimes_{\mathbb{Z}_p}H_1$ matching $F$, $V$, $L$ with Frobenius, Verschiebung and the Fontaine–Hodge submodule attached to `includeRight`, and the $k$-action with the maps induced by $\theta$. Let $c$ be a $1$-cocycle of the local group at $p$ valued in the restriction of $\mathrm{ad}\,\bar\rho$ along `primeLocalToGlobal`, and assume `IsLocallyFlatCocycleAd`: the twisted module $(\bar V\oplus\bar V,\ \sigma\mapsto(\rho(\sigma)x_1,\ c(\sigma)\rho(\sigma)x_1+\rho(\sigma)x_2))$ is realised by the points of some finite flat cocommutative Hopf $\mathbb{Z}_p$-algebra as in (a). Then there exist a finite free cocommutative Hopf algebra $H$ over $\mathbb{Z}_p$ of $p$-power rank whose reduction has local Cartier dual, a bijection $e$ from its convolution monoid of points onto $\bar V\times\bar V$ carrying convolution to addition and equivariant for the twisted action `dualLiftModuleActAd p c`, a coefficient map $\theta_H\colon k\to\mathrm{End}_{\mathrm{bialg}}(H)$ inducing the $k$-scalars through $e$, bialgebra maps $\pi\colon H\to H_1$ and $j\colon H_1\to H$ such that precomposition with $\pi$ corresponds under $e$, $e_1$ to $v\mapsto(0,v)$ and precomposition with $j$ to taking the first component, a finite-dimensional $k$-space $E$ with a Honda system $\mathcal E$ with parameter $0$ and an additive isomorphism $\iota_E$ of $E$ with the Dieudonné module of $(\mathbb{Z}/p)\otimes_{\mathbb{Z}_p}H$ matching $F$, $V$, $L$ and the $k$-action as in (c), $k$-linear maps $i\colon D\to E$ and $q\colon E\to D$ compatible via $\iota,\iota_E$ with the Dieudonné maps induced by $j$ and $\pi$ respectively, a pair $(X,Y)$ of endomorphisms of $D$ lying in $\mathcal H$.`extPairs`, that is $F\circ Y+X\circ V=0$ and $V\circ X+Y\circ F=0$, and a $k$-linear isomorphism $\Psi\colon E\to D\times D$ with $\Psi(i x)=(x,0)$, second component $q$, $\Psi(F z)=(F(\Psi z)_1+X(\Psi z)_2,\ F(\Psi z)_2)$, $\Psi(Vz)=(V(\Psi z)_1+Y(\Psi z)_2,\ V(\Psi z)_2)$, and $z\in\mathcal E.L$ exactly when both components of $\Psi z$ lie in $\mathcal H.L$.
--
--   This is the existence half of the Fontaine–Conrad comparison between locally flat first-order deformations of $\bar\rho$ at $p$ and self-extensions of the Honda system of the chosen finite flat model: a locally flat cocycle $c$ is turned into a finite flat Hopf algebra with $k$-coefficients, an extension of Honda systems, and a matrix pair $(X,Y)$ in the extension module `extPairs`. It is used by [`ResidualGaloisRep.exists_injective_flatClassSet_selfExt_of_hondaSystem_model`](thm.html#ResidualGaloisRep.exists_injective_flatClassSet_selfExt_of_hondaSystem_model), where the resulting classes are shown to separate locally flat cocycles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_fontaineConradPresentation_of_isLocallyFlatCocycleAd.lean

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

theorem ResidualGaloisRep.exists_fontaineConradPresentation_of_isLocallyFlatCocycleAd
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
    (hD : Module.finrank k D = 2)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (hc : ρbar.IsLocallyFlatCocycleAd p c) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H) (_ : Module.Finite ℤ_[p] H)
      (_ : Module.Free ℤ_[p] H) (_ : Coalgebra.IsCocomm ℤ_[p] H)
      (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V)
      (θH : k → (H →ₐc[ℤ_[p]] H)) (π : H →ₐc[ℤ_[p]] H₁) (j : H₁ →ₐc[ℤ_[p]] H)
      (E : Type) (_ : AddCommGroup E) (_ : Module k E) (_ : FiniteDimensional k E)
      (𝓔 : Deformation.HondaSystem (0 : k) E)
      (ιE : E ≃+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H))
      (i : D →ₗ[k] E) (q : E →ₗ[k] D)
      (XY : Module.End k D × Module.End k D) (Ψ : E ≃ₗ[k] D × D),
      (∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a) ∧
      IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H)) ∧
      (∀ f g, e (f * g) = e f + e g) ∧
      (∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
          e g = ρbar.dualLiftModuleActAd p c σ (e f)) ∧
      (∀ (a : k) (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        e (WithConv.toConv ((WithConv.ofConv f).comp (θH a : H →ₐ[ℤ_[p]] H))) = a • e f) ∧
      (∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
        e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[ℤ_[p]] H₁))) = (0, e₁ f)) ∧
      (∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        e₁ (WithConv.toConv ((WithConv.ofConv f).comp (j : H₁ →ₐ[ℤ_[p]] H))) = (e f).1) ∧
      (∀ z, ιE (𝓔.F z) =
        Deformation.DieudonneModule.frobenius (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ιE z)) ∧
      (∀ z, ιE (𝓔.V z) =
        Deformation.DieudonneModule.verschiebung (ZMod p) p ((ZMod p) ⊗[ℤ_[p]] H) (ιE z)) ∧
      (∀ z, z ∈ 𝓔.L ↔ ιE z ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H).toRingHom) ∧
      (∀ (a : k) (z : E), ιE (a • z) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θH a)) (ιE z)) ∧
      (∀ x : D, ιE (i x) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) j) (ι x)) ∧
      (∀ z : E, ι (q z) = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π) (ιE z)) ∧
      XY ∈ 𝓗.extPairs ∧
      (∀ x, Ψ (i x) = (x, 0)) ∧ (∀ z, (Ψ z).2 = q z) ∧
      (∀ z, Ψ (𝓔.F z) = (𝓗.F (Ψ z).1 + XY.1 (Ψ z).2, 𝓗.F (Ψ z).2)) ∧
      (∀ z, Ψ (𝓔.V z) = (𝓗.V (Ψ z).1 + XY.2 (Ψ z).2, 𝓗.V (Ψ z).2)) ∧
      (∀ z, z ∈ 𝓔.L ↔ ((Ψ z).1 ∈ 𝓗.L ∧ (Ψ z).2 ∈ 𝓗.L)) := by sorry
