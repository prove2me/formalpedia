-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_finiteFlat_padicInt_model_of_isLocallyFlatCocycleAd
-- name    : ResidualGaloisRep.exists_finiteFlat_padicInt_model_of_isLocallyFlatCocycleAd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/afbe707b-1f87-51fa-901d-ffec2b150cd6
-- title:
--   Finite flat model for ̄ V from a flat ad-cocycle
-- statement:
--   Let $k$ be a field, $p$ a prime, and $\bar\rho$ a residual Galois representation over $k$, i.e. a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\bar\rho\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{End}_k V$ that is trivial on the automorphisms fixing some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$ pointwise. Let $c$ be a $1$-cocycle for the restriction, along the map $\mathrm{Gal}(\overline{\mathbb Q_p}/\mathbb Q_p) \to \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ given by restriction of scalars followed by restriction to the algebraic closure of $\mathbb Q$, of the adjoint representation $\sigma \mapsto (f \mapsto \bar\rho(\sigma)\, f\, \bar\rho(\sigma^{-1}))$ on $\mathrm{End}_k V$. Assume the hypothesis `IsLocallyFlatCocycleAd`: there are a commutative ring $G$ carrying a Hopf algebra structure over $\mathbb Z_p$, finite and flat as a $\mathbb Z_p$-module and cocommutative, and a bijection $e$ from the convolution monoid of $\mathbb Z_p$-algebra maps $G \to \overline{\mathbb Q_p}$ onto $V \times V$ carrying convolution to addition and satisfying: whenever $g(h) = \sigma(f(h))$ for all $h \in G$, with $\sigma$ a $\mathbb Q_p$-automorphism of $\overline{\mathbb Q_p}$, one has $e(g) = (\bar\rho(\sigma) x_1,\; c(\sigma)(\bar\rho(\sigma) x_1) + \bar\rho(\sigma) x_2)$ where $(x_1,x_2) = e(f)$. The conclusion asserts the existence of a commutative ring $H$ with a $\mathbb Z_p$-Hopf algebra structure, finite and flat over $\mathbb Z_p$ and cocommutative, and a bijection $e$ from the convolution monoid of $\mathbb Z_p$-algebra maps $H \to \overline{\mathbb Q_p}$ onto $V$ with $e(fg) = e(f) + e(g)$, such that for every $\mathbb Q_p$-automorphism $\sigma$ of $\overline{\mathbb Q_p}$ and all $f, g$ with $g(h) = \sigma(f(h))$ for all $h \in H$ one has $e(g) = \bar\rho(\sigma)(e(f))$, $\sigma$ acting through the local-to-global map.
--
--   This is the step passing from a finite flat model of the extension module $E_c = \bar V \oplus \varepsilon\bar V$ attached to a local adjoint cocycle to a finite flat model of $\bar V$ itself, with $G_{\mathbb Q_p}$ acting through $\bar\rho$; finite flat models over $\mathbb Z_p$ are recorded here as finite flat cocommutative Hopf algebras together with an additive, equivariant description of their $\overline{\mathbb Q_p}$-points. It feeds the construction of unramified scalar twists of locally flat adjoint cocycles in [`ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one`](thm.html#ResidualGaloisRep.exists_isLocallyFlatCocycleAd_smul_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_finiteFlat_padicInt_model_of_isLocallyFlatCocycleAd.lean

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
open scoped PadicInt

theorem ResidualGaloisRep.exists_finiteFlat_padicInt_model_of_isLocallyFlatCocycleAd
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (hc : ρbar.IsLocallyFlatCocycleAd p c) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.ρ (primeLocalToGlobal (pPrime p) σ) (e f) := by sorry
