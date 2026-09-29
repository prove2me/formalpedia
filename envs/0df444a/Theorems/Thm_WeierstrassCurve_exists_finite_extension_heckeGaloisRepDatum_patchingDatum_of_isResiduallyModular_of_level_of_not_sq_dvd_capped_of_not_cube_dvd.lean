-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finite_extension_heckeGaloisRepDatum_patchingDatum_of_isResiduallyModular_of_level_of_not_sq_dvd_capped_of_not_cube_dvd
-- name    : WeierstrassCurve.exists_finite_extension_heckeGaloisRepDatum_patchingDatum_of_isResiduallyModular_of_level_of_not_sq_dvd_capped_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/1e06103b-799d-57c3-b448-cb35f86d6526
-- title:
--   Hecke–Galois datum and patching datum over a finite extension
-- statement:
--   Fix an odd prime $p$ (so $p$ is prime and $p\neq 2$) and a Weierstrass curve $W$ over $\mathbb{Z}$ with $\Delta_W\neq 0$ which is a semistable model in the project's sense ($q\mid\Delta_W$ implies $q\nmid c_4$ for every prime $q$) and whose mod-$p$ representation is irreducible (`ModRepIsIrreducible`: the $\mathbb{Z}/p$-module of $p$-torsion points of $W$ over $\overline{\mathbb{Q}}$ has no proper non-zero Galois-stable submodule). Assume a non-zero witness level $M_0$ with `IsResiduallyModularOfLevel p M₀` — a normalised eigenform of weight $2$ on $\Gamma_0(M_0)$ and a maximal ideal $\mathfrak{m}\ni p$ of $\overline{\mathbb{Z}}\subset\mathbb{C}$ with $a_\ell(f)\equiv a_\ell(W)\pmod{\mathfrak{m}}$ for all primes $\ell\neq p$ of good reduction with $\ell\nmid M_0$ — subject to $p^2\nmid M_0$ and $q^3\nmid M_0$ for every prime $q\neq p$. Let $\mathcal{O}$ be a complete discrete valuation domain of characteristic $0$ with finite residue field and $p\in\mathfrak{m}_{\mathcal{O}}$. The conclusion asserts the existence of a ring $\mathcal{O}'$ of the same kind (complete discrete valuation domain, finite residue field, characteristic $0$) which is a module-finite $\mathcal{O}$-algebra along an injective local map, with $p\in\mathfrak{m}_{\mathcal{O}'}$, and of: a finite set $S$ of primes containing $p$ and every prime dividing $\Delta_W$; a non-zero level $N$ all of whose prime factors lie in $S$, with $q^2\mid N$ and $q^3\nmid N$ for all $q\in S\setminus\{p\}$, with $p\Vert N$ when $p\mid\Delta_W$ or $p\nmid a_p(W)$ and $p\nmid N$ when $p\nmid\Delta_W$ and $p\mid a_p(W)$; the property [`CuspForm.HasIntegralStructure N 2`](def/CuspForm_IntegralStructure.html#L6) (cusp forms with integral $q$-coefficients span the weight-$2$ space over $\mathbb{C}$); a ring homomorphism $\theta$ from the Hecke algebra `heckeAlgebra N 2 S` to the residue field of $\mathcal{O}'$ with $\theta(T_\ell)$ equal to the residue of $a_\ell(W)$ for every prime $\ell\nmid N$, $\ell\notin S$; and a complete local Noetherian $\mathcal{O}'$-algebra $T$, finite and free over $\mathcal{O}'$ along a local map, such that [`CuspForm.HeckeGaloisRepDatum N S 𝒪' θ T`](def/CuspForm_HeckeGaloisRepDatum.html#L8) is non-empty and, in addition, for every proof $hcard_1$ that the $p$-torsion of $W$ over $\overline{\mathbb{Q}}$ has cardinality $p^2$, every proof $hker$ that its mod-$p$ Galois representation factors through a finite level, every ring map $\iota:\mathbb{Z}/p\to$ the residue field of $\mathcal{O}'$ and every datum $H$ for $(N,S,\mathcal{O}',\theta,T)$, the following two clauses hold: in the case $p\mid\Delta_W$ or $p\nmid a_p(W)$ (respectively in the case $p\nmid\Delta_W$ and $p\mid a_p(W)$), for every [`GaloisRep.DeformationRingData`](def/GaloisRep_DeformationRingData.html#L8) $D$ over $\mathcal{O}'$ for the $\iota$-base change of the residual representation `residualGaloisRepOf` of $W$ with deformation condition [`GaloisRep.ordinaryCondition 𝒪' p S`](def/GaloisRep_LocalConditions.html#L28) (respectively [`GaloisRep.flatCondition 𝒪' p S`](def/GaloisRep_Flat.html#L47)), and every local $\mathcal{O}'$-algebra map $\varphi:D.R\to T$ carrying $D.\rho$ to a representation equivalent to $H.\rho$, there are a non-trivial abelian group $M$ that is both a $D.R$- and a $T$-module with the two actions compatible along $\varphi$, and an $r\in\mathbb{N}$ with [`Algebra.PatchingDatum 𝒪' p r D.R M`](def/Algebra_PatchingDatum.html#L39) non-empty. Note that $\iota$ and $H$ are arbitrary here, and that no isomorphism statement between $D.R$ and $T$ is asserted.
--
--   This is one of the inputs to modularity lifting for semistable elliptic curves at an odd prime in the style of Wiles and Taylor–Wiles, as surveyed in Darmon–Diamond–Taylor: the existence of a Hecke–Galois datum at a suitably chosen auxiliary level together with the Taylor–Wiles patching data attached to the corresponding ordinary or flat deformation problem. Compared with the textbook formulation, the residual modularity input is supplied as a concrete witness level $M_0$ with $p^2\nmid M_0$ and cube-free away from $p$, the produced level $N$ is constrained to be cube-free away from $p$, and the coefficient ring is allowed to grow to a finite injective local extension $\mathcal{O}'$ of $\mathcal{O}$ (the datum and the patching clause are packaged in a single existential because the ring $T$ is not determined in advance). It is used by the conductor-level modularity lifting statement for $p=3$ and $p=5$ ([`WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd`](thm.html#WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finite_extension_heckeGaloisRepDatum_patchingDatum_of_isResiduallyModular_of_level_of_not_sq_dvd_capped_of_not_cube_dvd.lean

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

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_finite_extension_heckeGaloisRepDatum_patchingDatum_of_isResiduallyModular_of_level_of_not_sq_dvd_capped_of_not_cube_dvd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p)
    (M₀ : ℕ) [NeZero M₀] (hres₀ : W.IsResiduallyModularOfLevel p M₀)
    (hM₀ : ¬ p ^ 2 ∣ M₀)
    (hM₀3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M₀)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪')
      (_ : Finite (IsLocalRing.ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪')),
    Function.Injective (algebraMap 𝒪 𝒪') ∧
    (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪' ∧
    ∃ (S : Finset ℕ) (_ : ∀ q ∈ S, q.Prime) (_ : p ∈ S)
      (_ : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S) (N : ℕ) (_ : NeZero N),
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) ∧
      (∀ q ∈ S, q ≠ p → q ^ 2 ∣ N) ∧
      (∀ q ∈ S, q ≠ p → ¬ q ^ 3 ∣ N) ∧
      ((¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → p ∣ N ∧ ¬ p ^ 2 ∣ N) ∧
      (W.IsGoodPrimeFor p → (p : ℤ) ∣ W.apOfModel p → ¬ p ∣ N) ∧
      CuspForm.HasIntegralStructure N 2 ∧
      ∃ θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪',
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
            θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) =
              IsLocalRing.residue 𝒪' ((W.apOfModel ℓ : ℤ) : 𝒪')) ∧
        ∃ (T : Type) (_ : CommRing T) (_ : IsLocalRing T) (_ : IsNoetherianRing T)
          (_ : IsAdicComplete (IsLocalRing.maximalIdeal T) T) (_ : Algebra 𝒪' T)
          (_ : IsLocalHom (algebraMap 𝒪' T)) (_ : Module.Finite 𝒪' T) (_ : Module.Free 𝒪' T),
          Nonempty (CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪' θ T) ∧
          ∀ (hcard₁ : Nat.card (Submodule.torsionBy ℤ
                ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
            (hker : GaloisFactorsThroughFiniteLevel
                (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
                  (W.map (Int.castRingHom ℚ)) p))
            (ι : ZMod p →+* IsLocalRing.ResidueField 𝒪')
            (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪' θ T),
            ((¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) →
              ∀ (D : GaloisRep.DeformationRingData 𝒪'
                  (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).baseChangeAlong ι)
                  (GaloisRep.ordinaryCondition 𝒪' p S))
                (φ : D.R →ₐ[𝒪'] T) (hφ : IsLocalHom (φ : D.R →+* T)),
                (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ →
                ∃ (M : Type) (_ : AddCommGroup M) (_ : Module D.R M) (_ : Module T M)
                  (_ : Nontrivial M),
                  (∀ (x : D.R) (m : M), φ x • m = x • m) ∧
                  ∃ r : ℕ, Nonempty (Algebra.PatchingDatum 𝒪' p r D.R M)) ∧
            (W.IsGoodPrimeFor p → (p : ℤ) ∣ W.apOfModel p →
              ∀ (D : GaloisRep.DeformationRingData 𝒪'
                  (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).baseChangeAlong ι)
                  (GaloisRep.flatCondition 𝒪' p S))
                (φ : D.R →ₐ[𝒪'] T) (hφ : IsLocalHom (φ : D.R →+* T)),
                (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ →
                ∃ (M : Type) (_ : AddCommGroup M) (_ : Module D.R M) (_ : Module T M)
                  (_ : Nontrivial M),
                  (∀ (x : D.R) (m : M), φ x • m = x • m) ∧
                  ∃ r : ℕ, Nonempty (Algebra.PatchingDatum 𝒪' p r D.R M)) := by sorry
