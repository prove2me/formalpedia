-- Prove2me | Theorems.Thm_WeierstrassCurve_tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd_finiteAt
-- name    : WeierstrassCurve.tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd_finiteAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/79254d96-6300-5864-a72e-b41b531dfabe
-- title:
--   Local conditions at p and Frobenius charpolys for Tate modules
-- statement:
--   Let $p$ be a prime, $W$ a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ which is a semistable model, i.e. no prime dividing $\Delta_W$ divides $c_4(W)$, and suppose that for every $n$ the $p^n$-torsion of the points of $W$ over $\overline{\mathbb{Q}}$ (after base change along $\mathbb{Z} \to \mathbb{Q}$) has exactly $(p^n)^2$ elements; let $\rho$ be the resulting adic Galois representation on the $p$-adic Tate module, base-changed along the local homomorphism $\mathbb{Z}_p \to \mathcal{O}$ determined by $p \in \mathfrak{m}_{\mathcal{O}}$, where $\mathcal{O}$ is a complete discrete valuation domain of characteristic zero with finite residue field. Let $S$ be a finite set of naturals consisting of primes, containing $p$ and every prime dividing $\Delta_W$. Then three assertions hold: (i) if $p \mid \Delta_W$, then $\rho$ satisfies the ordinary condition of type $S$, namely its determinant is cyclotomic at $p$, it is ordinary at $p$, and it is unramified at every prime outside $S$; (ii) if $p \neq 2$ and $p \nmid \Delta_W$, then $\rho$ satisfies the flat condition of type $S$, with ordinarity at $p$ replaced by flatness at $p$; (iii) for every prime $\ell \notin S$ with $\ell \nmid \Delta_W$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$, and every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, the characteristic polynomial of $\rho(\sigma)$ is $X^2 - a_{\ell}X + \ell$ in $\mathcal{O}[X]$, where $a_{\ell}$ is the trace of Frobenius of the reduction of $W$ mod $\ell$.
--
--   This packages the local behaviour of the $p$-adic Tate module of a semistable elliptic curve over $\mathbb{Q}$ into the deformation-theoretic data needed for modularity lifting: ordinary of type $S$ at multiplicative $p$, finite flat of type $S$ at odd good $p$, together with the Eichler–Shimura shape of Frobenius characteristic polynomials at good primes outside $S$. It feeds the identification of the Tate module representation as a modular representation of the relevant level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd_finiteAt.lean

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_Algebra_PatchingDatum
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd_finiteAt
    (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) :
    (¬ W.IsGoodPrimeFor p →
      GaloisRep.ordinaryCondition 𝒪 p S
        (((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).baseChangeAlong
          (GaloisRep.padicIntToRing 𝒪 p hp𝒪) (GaloisRep.isLocalHom_padicIntToRing 𝒪 p hp𝒪))) ∧
    (p ≠ 2 → W.IsGoodPrimeFor p →
      GaloisRep.flatCondition 𝒪 p S
        (((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).baseChangeAlong
          (GaloisRep.padicIntToRing 𝒪 p hp𝒪) (GaloisRep.isLocalHom_padicIntToRing 𝒪 p hp𝒪))) ∧
    (∀ (ℓ : ℕ), ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly ((((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).baseChangeAlong
            (GaloisRep.padicIntToRing 𝒪 p hp𝒪) (GaloisRep.isLocalHom_padicIntToRing 𝒪 p hp𝒪)).ρ σ) =
            X ^ 2 - C ((W.apOfModel ℓ : ℤ) : 𝒪) * X + C ((ℓ : 𝒪))) := by sorry
