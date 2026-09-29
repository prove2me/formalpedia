-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_hondaSystem_finrank_endHonda_le_injective_of_isLocalRing_cartierDual
-- name    : ResidualGaloisRep.exists_hondaSystem_finrank_endHonda_le_injective_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/2b24356e-6a2a-5d95-bae8-8f97f7eedce1
-- title:
--   Honda-system model bounding local flat classes of ad ρ̄
-- statement:
--   Let $k$ be a finite field of characteristic $p$, with $p$ an odd prime, and fix a $\mathbb{Z}_p$-algebra structure on $\mathbb{Z}/p$ whose structure map has kernel the ideal $(p)$. Let $\bar\rho$ be a residual Galois representation over $k$, that is, a $k$-vector space $V$ with $\dim_k V = 2$ together with a homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{End}_k V$ factoring through a finite level. Assume there is a commutative ring $H$ carrying a cocommutative Hopf algebra structure over $\mathbb{Z}_p$, finite and flat as a $\mathbb{Z}_p$-module, such that the Cartier dual (the $\mathbb{Z}/p$-linear dual) of $(\mathbb{Z}/p)\otimes_{\mathbb{Z}_p} H$ is a local ring, and a bijection $e$ from the set of $\mathbb{Z}_p$-algebra maps $H \to \overline{\mathbb{Q}_p}$, equipped with its convolution multiplication, onto $V \times V$, which turns convolution into addition and is equivariant for $\mathrm{Gal}(\overline{\mathbb{Q}_p}/\mathbb{Q}_p)$: if $g = \sigma \circ f$ pointwise then $e(g) = \mathrm{dualLiftModuleActAd}$ at the zero cocycle applied to $e(f)$, i.e. the diagonal action of $\sigma$ on $V\times V$ through $\rho$ restricted along the local-to-global map at $p$. Then there exist a finite-dimensional $k$-vector space $D$ and a Honda system $\mathcal{H}$ over $k$ with parameter $\ell = 0$ on $D$ — maps $F, V_{\mathcal H} \in \mathrm{End}_k D$ with $F \circ V_{\mathcal H} = V_{\mathcal H} \circ F = 0$ and a submodule $L$ with $L \cap \mathrm{range}\,F$ killed by the first axiom, $\mathrm{range}\,F + L = D$ and $V_{\mathcal H}$ injective on $L$ — such that $\dim_k D = 2$; the space $\mathcal{H}.\mathrm{endHonda}$ of endomorphisms of $D$ preserving $L$ and commuting with $F$ and $V_{\mathcal H}$ has dimension at most that of the invariants of $\mathrm{ad}\,\bar\rho$ restricted to the local Galois group at $p$; and there is an injective $k$-linear map from the span of the classes of locally flat cocycles in $H^1$ of this restricted adjoint representation into $\mathcal{H}.\mathrm{selfExt}$, the module of pairs $(X,Y)$ of endomorphisms of $D$ with $F\circ Y + X\circ V_{\mathcal H} = 0$ and $V_{\mathcal H}\circ X + Y\circ F = 0$ modulo the pullback of the submodule `innerPairs`.
--
--   This is the unipotent branch of the Fontaine-theoretic bound on flat deformation classes at $p$: it converts a finite flat $\mathbb{Z}_p$-model of $\bar V \oplus \bar V$ with local Cartier dual of its special fibre into a rank-two $k$-Honda system whose endomorphisms bound $H^0(\mathbb{Q}_p, \mathrm{ad}\,\bar\rho)$ and whose self-extension module receives the local flat classes. It feeds the finiteness and dimension estimate for the local flat classes used in the deformation-theoretic bookkeeping of the modularity lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_hondaSystem_finrank_endHonda_le_injective_of_isLocalRing_cartierDual.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_HondaSelfExt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.exists_hondaSystem_finrank_endHonda_le_injective_of_isLocalRing_cartierDual
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
    ∃ (D : Type) (_ : AddCommGroup D) (_ : Module k D) (_ : FiniteDimensional k D)
      (𝓗 : Deformation.HondaSystem (0 : k) D),
      Module.finrank k D = 2 ∧
      Module.finrank k 𝓗.endHonda ≤
        Module.finrank k (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)).ρ.invariants ∧
      ∃ f : ρbar.localFlatClassesAd p →ₗ[k] 𝓗.selfExt, Function.Injective f := by sorry
