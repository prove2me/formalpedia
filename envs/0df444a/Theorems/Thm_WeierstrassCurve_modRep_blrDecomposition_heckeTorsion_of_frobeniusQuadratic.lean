-- Prove2me | Theorems.Thm_WeierstrassCurve_modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic
-- name    : WeierstrassCurve.modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/7831bc51-dc5e-56e9-ac22-2bd5697e5ee0
-- title:
--   Boston–Lenstra–Ribet decomposition of the Hecke 𝔪-torsion
-- statement:
--   Let $E$ be an elliptic curve over $\mathbb{Q}$ and let $W$ be a Weierstrass curve over $\mathbb{Z}$ which is an integral model of $E$, in the sense that some variable change over $\mathbb{Q}$ carries $E$ to the base change of $W$ to $\mathbb{Q}$; let $p \neq 2$ be a prime. Let $J$ be an abelian group carrying a module structure over $\mathbb{T} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$ together with a distributive action of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ commuting with the $\mathbb{T}$-action, let $M > 0$, and let $\mathfrak{m}$ be a maximal ideal of $\mathbb{T}$ whose residue ring $\mathbb{T}/\mathfrak{m}$ has characteristic $p$. Assume: the $p$-torsion of $E(\overline{\mathbb{Q}})$ is nontrivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $\bot$ and $\top$; the homomorphism `galoisRepModuleEnd` giving the Galois action on this $p$-torsion kills the absolute Galois group of some finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$; for every prime $\ell$ with $\ell \nmid \Delta(W)$, $\ell \nmid M$ and $\ell \neq p$, the element $X_\ell - a_\ell$ lies in $\mathfrak{m}$, where $a_\ell$ is the trace of Frobenius of the reduction of $W$ modulo $\ell$; the Eichler–Shimura relation $\sigma^2 x - X_\ell \cdot (\sigma x) + \ell x = 0$ holds for every prime $\ell \nmid Mp$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$, every $\sigma$ that is a Frobenius at $\ell$ for $A$, and every $p$-power torsion element $x \in J$; the Galois action on the $\mathfrak{m}$-torsion $J[\mathfrak{m}] = \{x : \mathfrak{m}x = 0\}$ likewise kills the Galois group of a finite extension of $\mathbb{Q}$; and $J[\mathfrak{m}]$ is finite. Fix a basis $b$ of $E[p]$ over $\mathbb{Z}/p$ indexed by $\mathrm{Fin}\,2$. Then there are $n \in \mathbb{N}$ and a $\mathbb{T}/\mathfrak{m}$-linear isomorphism $e : J[\mathfrak{m}] \to (\mathbb{T}/\mathfrak{m})^{2}{}^{\oplus n}$ such that for every $\sigma$ in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, every $w \in J[\mathfrak{m}]$ and every index $i < n$, the $i$-th component of $e(\sigma w)$ is obtained from the $i$-th component of $e(w)$ by multiplication with the $2 \times 2$ matrix of $\sigma$ acting on $E[p]$ in the basis $b$, with entries pushed forward along the ring map $\mathbb{Z}/p \to \mathbb{T}/\mathfrak{m}$.
--
--   This is the Boston–Lenstra–Ribet multiplicity statement: under an absolute irreducibility coming from irreducibility and oddness of the mod $p$ representation of $E$, the $\mathfrak{m}$-torsion of a Hecke module with Eichler–Shimura relations is a direct sum of copies of that representation. It is stated here for an arbitrary integral Weierstrass model, and is used in the realisation of mod $p$ representations in Jacobians of modular curves and in the construction of torsion at lower level, i.e. on the level-lowering side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic.lean

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FreyPackage_MazurAttachmentApparatus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (W : WeierstrassCurve ℤ) (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    {M : ℕ} (hM : 0 < M) (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) [CharP (HeckeAlg ⧸ 𝔪) p]
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ E p)
    (hker : GaloisFactorsThroughFiniteLevel
      (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p))
    (hcong : FreyPackage.IdealGoodPrimeCurveCongruence p M W 𝔪)
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) M p J)
    (hcont : GaloisFactorsThroughFiniteLevel
      (mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J 𝔪))
    (hfin : Finite (heckeTorsion J 𝔪))
    (b : Module.Basis (Fin 2) (ZMod p) (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p)) :
    ∃ (n : ℕ) (e : heckeTorsion J 𝔪 ≃ₗ[HeckeAlg ⧸ 𝔪] (Fin n → (Fin 2 → HeckeAlg ⧸ 𝔪))),
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : heckeTorsion J 𝔪) (i : Fin n),
        e (mTorsionGaloisRep J 𝔪 σ w) i
          = (((((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom).comp
                (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p)) σ).map
              (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))).mulVec (e w i) := by sorry
