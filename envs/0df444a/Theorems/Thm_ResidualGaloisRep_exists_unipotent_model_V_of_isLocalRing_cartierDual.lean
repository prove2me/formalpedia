-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_unipotent_model_V_of_isLocalRing_cartierDual
-- name    : ResidualGaloisRep.exists_unipotent_model_V_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/137d448a-f592-5ac0-915c-62bc93e66097
-- title:
--   Unipotent finite flat model of ̄ V from one of ̄ V⊕̄ V
-- statement:
--   Let $k$ be a finite field of characteristic $p$ with $p$ an odd prime, and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ of dimension $2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}$-type automorphism group $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_k V$ which is trivial on the automorphisms fixing some finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$. Write $\Gamma_p$ for the group of $\mathbb Q_p$-algebra automorphisms of `PadicAlgCl p` and $\Gamma_p \to \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ for the restriction map `primeLocalToGlobal`. Assume there is a commutative ring $H$ carrying a $\mathbb Z_p$-Hopf algebra structure, finite and flat and cocommutative over $\mathbb Z_p$, such that the Cartier dual (the $\mathbb Z/p$-linear dual) of $\mathbb Z/p\otimes_{\mathbb Z_p} H$ is a local ring, and a bijection $e$ from `WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)` onto $V\times V$ with $e(fg)=e(f)+e(g)$ and $e(\sigma\circ f)=\bar\rho.\mathrm{dualLiftModuleActAd}\,p\,0\,\sigma(e(f))$ for $\sigma\in\Gamma_p$, which for the zero cocycle is the diagonal action $x\mapsto(\rho(\sigma)x_1,\rho(\sigma)x_2)$. Then there is a commutative ring $H_1$ with a $\mathbb Z_p$-Hopf algebra structure, finite, free and cocommutative over $\mathbb Z_p$, with $\mathrm{rk}_{\mathbb Z_p}H_1=|k|^2$, whose mod-$p$ Cartier dual is again local, and a bijection $e_1$ from `WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)` onto $V$ with $e_1(fg)=e_1(f)+e_1(g)$ and $e_1(\sigma\circ f)=\rho(\sigma|_{\overline{\mathbb Q}})\,e_1(f)$ for all $\sigma\in\Gamma_p$.
--
--   This descends a unipotent finite flat $\mathbb Z_p$-model of the doubled local module $\bar V\oplus\bar V$ to a unipotent finite flat model of $\bar V$ itself, of the expected rank $|\bar V|=|k|^2$; unipotence is encoded as locality of the Cartier dual of the special fibre. It feeds the construction of a Honda system attached to $\bar\rho$ at $p$, used in the flat local deformation condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_unipotent_model_V_of_isLocalRing_cartierDual.lean

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

theorem ResidualGaloisRep.exists_unipotent_model_V_of_isLocalRing_cartierDual
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
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f)) :
    ∃ (H₁ : Type) (_ : CommRing H₁) (_ : HopfAlgebra ℤ_[p] H₁) (_ : Module.Finite ℤ_[p] H₁)
      (_ : Module.Free ℤ_[p] H₁) (_ : Coalgebra.IsCocomm ℤ_[p] H₁),
      Module.finrank ℤ_[p] H₁ = Nat.card k ^ 2 ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H₁)) ∧
      ∃ e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V,
        (∀ f g, e₁ (f * g) = e₁ f + e₁ g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H₁, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e₁ g = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (e₁ f) := by sorry
