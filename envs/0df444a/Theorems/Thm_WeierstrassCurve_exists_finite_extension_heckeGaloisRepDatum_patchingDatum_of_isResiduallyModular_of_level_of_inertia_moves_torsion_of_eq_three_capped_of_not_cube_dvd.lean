-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_finite_extension_heckeGaloisRepDatum_patchingDatum_of_isResiduallyModular_of_level_of_inertia_moves_torsion_of_eq_three_capped_of_not_cube_dvd
-- name    : WeierstrassCurve.exists_finite_extension_heckeGaloisRepDatum_patchingDatum_of_isResiduallyModular_of_level_of_inertia_moves_torsion_of_eq_three_capped_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/7b87af13-0576-5d7a-9227-3ba405bde7bd
-- title:
--   Hecke–Galois datum and patching datum at p=3, cube-free level
-- statement:
--   Let $p$ be a prime with $p\neq 2$ and $p=3$, and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W\neq 0$ which is a semistable model in the project's sense ($q\mid\Delta_W$ implies $q\nmid c_4$ for every prime $q$) and whose mod-$p$ torsion representation is irreducible in the sense of the project predicate `ModRepIsIrreducible`. Assume $W$ is residually modular of level $M_0\ge 1$, i.e. there are a normalised weight-$2$ eigenform on $\Gamma_0(M_0)$ and a maximal ideal $\mathfrak m$ of the integral closure of $\mathbb Z$ in $\mathbb C$ containing $p$ such that for every prime $\ell$ with $\ell\nmid\Delta_W$, $\ell\nmid M_0$, $\ell\neq p$ the $\ell$-th $q$-coefficient is congruent mod $\mathfrak m$ to $a_\ell(W)=\mathrm{tr}\,\mathrm{Frob}_\ell$ of the reduction; assume further that if $p^2\mid M_0$ then no nonzero $p$-torsion point of $W$ over $\overline{\mathbb Q}$ is fixed by a full inertia subgroup at $p$, and that $q^3\nmid M_0$ for every prime $q\neq p$. Let $\mathcal O$ be a complete discrete valuation ring of characteristic $0$ with finite residue field and $p$ in its maximal ideal. The conclusion asserts: there is a ring $\mathcal O'$ with the same list of properties, module-finite over $\mathcal O$ via an injective local $\mathcal O$-algebra structure with $p\in\mathfrak m_{\mathcal O'}$, together with a finite set $S$ of primes containing $p$ and all primes dividing $\Delta_W$, and a level $N\ge 1$ whose prime divisors lie in $S$, with $q^2\mid N$ and $q^3\nmid N$ for all $q\in S\setminus\{p\}$, with $p\mid N$ and $p^2\nmid N$ when $p\mid\Delta_W$ or $p\nmid a_p(W)$, and $p\nmid N$ when $p\nmid\Delta_W$ and $p\mid a_p(W)$; the weight-$2$ forms of level $N$ have an integral structure (the $\mathbb Z$-span of forms with integral $q$-coefficients spans over $\mathbb C$); and there is a ring homomorphism $\theta$ from the Hecke algebra [`CuspForm.heckeAlgebra N 2 S`](def/CuspForm_HeckeAlgebra.html#L18) to the residue field of $\mathcal O'$ with $\theta(T_\ell)=a_\ell(W)\bmod\mathfrak m_{\mathcal O'}$ for all primes $\ell\notin S$, $\ell\nmid N$. Finally there is a complete local Noetherian ring $T$, finite and free as an $\mathcal O'$-module via a local $\mathcal O'$-algebra structure, such that [`CuspForm.HeckeGaloisRepDatum N S 𝒪' θ T`](def/CuspForm_HeckeGaloisRepDatum.html#L8) is nonempty and, for every proof that the $p$-torsion of $W$ over $\overline{\mathbb Q}$ has cardinality $p^2$, every proof that the mod-$p$ representation factors through a finite level, every ring homomorphism $\iota:\mathbb Z/p\to$ the residue field of $\mathcal O'$ and every datum $H$ of that Hecke–Galois type, the following patching clause holds in two cases: in the case $p\mid\Delta_W$ or $p\nmid a_p(W)$ for the ordinary condition [`GaloisRep.ordinaryCondition 𝒪' p S`](def/GaloisRep_LocalConditions.html#L28) (cyclotomic determinant, ordinary at $p$, unramified outside $S$), and in the case $p\nmid\Delta_W$, $p\mid a_p(W)$ for [`GaloisRep.flatCondition 𝒪' p S`](def/GaloisRep_Flat.html#L47) (cyclotomic determinant, flat at $p$, unramified outside $S$): for every universal deformation datum $D$ of the base change along $\iota$ of the residual representation of $W$ of that type, and every local $\mathcal O'$-algebra map $\varphi:D.R\to T$ carrying the universal deformation to $H.\rho$ up to equivalence, there exist a nontrivial abelian group $M$ with compatible $D.R$- and $T$-module structures (compatible along $\varphi$) and an $r$ with [`Algebra.PatchingDatum 𝒪' p r D.R M`](def/Algebra_PatchingDatum.html#L39) nonempty.
--
--   This packages the automorphic and patching inputs of modularity lifting for semistable elliptic curves at $p=3$, in the shape needed to run the Taylor–Wiles argument (Wiles 1995, Taylor–Wiles 1995, as surveyed in Darmon–Diamond–Taylor). It differs from a textbook statement in several ways: the residual modularity is supplied at a specific level $M_0$ subject to an inertia hypothesis at $p$ and to $q^3\nmid M_0$ away from $p$, the produced Taylor–Wiles level $N$ is correspondingly capped ($q^2\mid N$ but $q^3\nmid N$ off $p$), the coefficient ring is allowed to grow to a finite injective local extension $\mathcal O'$ of $\mathcal O$, and the patching conclusion is not an isomorphism statement but the existence of a patching datum in the project's sense for every deformation ring mapping onto the Hecke ring compatibly with the given representations. It is used by [`WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd`](thm.html#WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd), which combines it with the composition theorem to obtain a modular model of exact conductor level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_finite_extension_heckeGaloisRepDatum_patchingDatum_of_isResiduallyModular_of_level_of_inertia_moves_torsion_of_eq_three_capped_of_not_cube_dvd.lean

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

theorem WeierstrassCurve.exists_finite_extension_heckeGaloisRepDatum_patchingDatum_of_isResiduallyModular_of_level_of_inertia_moves_torsion_of_eq_three_capped_of_not_cube_dvd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p = 3) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p)
    (M₀ : ℕ) [NeZero M₀] (hres₀ : W.IsResiduallyModularOfLevel p M₀)
    (hns : p ^ 2 ∣ M₀ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) → x = 0)

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
