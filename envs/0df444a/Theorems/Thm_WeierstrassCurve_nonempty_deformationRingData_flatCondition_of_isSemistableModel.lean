-- Prove2me | Theorems.Thm_WeierstrassCurve_nonempty_deformationRingData_flatCondition_of_isSemistableModel
-- name    : WeierstrassCurve.nonempty_deformationRingData_flatCondition_of_isSemistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/d0fa61ca-00f3-5f36-9e8a-ace149f5dbf8
-- title:
--   Representability of the flat deformation problem for ρ̄_{E,p}
-- statement:
--   Let $p$ be a prime (as a `Fact`) with $p \neq 2$, and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $W.\Delta \neq 0$ which is a semistable model in the project's sense, i.e. no prime dividing $\Delta$ divides $c_4$. Assume the $p$-torsion of the points of $W \otimes \mathbb{Q}$ over $\overline{\mathbb{Q}}$ (`Submodule.torsionBy ℤ … p`) has cardinality exactly $p^2$, and that the associated action homomorphism `galoisRepModuleEnd` factors through a finite level, meaning there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every automorphism fixing $L$ pointwise acts as the identity on this $p$-torsion; these two data define the residual representation $\bar\rho_0 =$ `residualGaloisRepOf` over $\mathbb{Z}/p$, whose underlying space is that torsion group. Let $S$ be a finite set of primes containing $p$ and containing every prime dividing $\Delta$. Let $\mathcal{O}$ be a characteristic-zero complete discrete valuation ring (a domain, discrete valuation ring, adically complete for its maximal ideal) with finite residue field, with $p$ in the maximal ideal, and let $\iota : \mathbb{Z}/p \to k_{\mathcal{O}}$ be a ring homomorphism; write $\bar\rho$ for the base change of $\bar\rho_0$ along $\iota$, assumed absolutely irreducible (irreducible after base change to an algebraic closure of $k_{\mathcal{O}}$). Finally assume $p \nmid \Delta$ and $p \mid$ `W.apOfModel p`, the trace of Frobenius of the reduction at $p$. The conclusion is that the type [`GaloisRep.DeformationRingData 𝒪 ρbar (GaloisRep.flatCondition 𝒪 p S)`](def/GaloisRep_DeformationRingData.html#L8) is nonempty: there exist a local Noetherian adically complete $\mathcal{O}$-algebra $R$ with local structure map and residue-field surjectivity, together with an adic representation $\rho$ over $R$ satisfying the flat condition (cyclotomic determinant, finite flat at $p$ at every finite quotient level in the sense of `IsFlatAt`, unramified outside $S$) whose residual representation is equivalent to $\bar\rho$ base-changed to $k_R$, and which is universal: every such deformation over such an $A$ is obtained from $\rho$ by a unique local $\mathcal{O}$-algebra map $R \to A$ up to equivalence.
--
--   Classically this is Mazur's representability theorem for the flat deformation problem of an absolutely irreducible residual representation, the deformation-condition axioms for finite flat group schemes going back to Ramakrishna's variant of Mazur's functor; it is the input at $p$ for modularity lifting in the good supersingular case, as surveyed in Darmon–Diamond–Taylor. The formal statement is shaped as the nonemptiness of the project structure [`GaloisRep.DeformationRingData`](def/GaloisRep_DeformationRingData.html#L8), which bundles the universal ring, the universal adic representation, the identification of its residual representation with $\bar\rho$, and the universal property; the local condition is the project's [`GaloisRep.flatCondition`](def/GaloisRep_Flat.html#L47), namely cyclotomic determinant, `IsFlatAt p` (each finite level of the representation comes from the $\overline{\mathbb{Q}}$-points of a finite flat cocommutative Hopf algebra over the rationals with denominators coprime to $p$) and unramifiedness outside $S$. It is used in the two modularity-lifting statements for semistable curves at $p = 3$ and $p = 5$ that conclude [`Mlc1IsModularModelOfExactConductorLevel W`](def/WeierstrassCurve_Mlc1RowStatement.html#L9).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_nonempty_deformationRingData_flatCondition_of_isSemistableModel.lean

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

theorem WeierstrassCurve.nonempty_deformationRingData_flatCondition_of_isSemistableModel (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (ι : ZMod p →+* IsLocalRing.ResidueField 𝒪)
    (habs : (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).baseChangeAlong
      ι).IsAbsolutelyIrreducible)
    (hgood : W.IsGoodPrimeFor p) (hss : (p : ℤ) ∣ W.apOfModel p) :
    Nonempty (GaloisRep.DeformationRingData 𝒪
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).baseChangeAlong ι)
      (GaloisRep.flatCondition 𝒪 p S)) := by sorry
