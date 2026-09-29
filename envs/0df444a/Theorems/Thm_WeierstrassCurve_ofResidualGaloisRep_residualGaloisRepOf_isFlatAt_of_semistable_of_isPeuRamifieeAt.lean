-- Prove2me | Theorems.Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_semistable_of_isPeuRamifieeAt
-- name    : WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_semistable_of_isPeuRamifieeAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/084dd287-e6c8-5526-b031-c3f15ca7294e
-- title:
--   Flatness at p of ρ̄_{W,p}⊗ k for semistable peu ramifiée W
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $p$ be a prime, let $k$ be a finite field and let $\iota\colon \mathbb{Z}/p \to k$ be a ring homomorphism. Assume: the discriminant satisfies $W.\Delta \neq 0$; if $p \mid W.\Delta$ then $p \nmid W.c_4$; the base change $W_{\mathbb{Q}}$ of $W$ along $\mathbb{Z}\to\mathbb{Q}$ satisfies `IsPeuRamifieeAt p p`, i.e. $p \mid v_p(W.\Delta)$; the group $\operatorname{Tors}_p$ of $p$-torsion points of $W_{\mathbb{Q}}$ over $\overline{\mathbb{Q}}$ has cardinality $p^2$; and the monoid homomorphism `galoisRepModuleEnd` giving the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $\operatorname{Tors}_p$ by $\mathbb{Z}/p$-endomorphisms kills the absolute Galois group of some finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$. The last two hypotheses make `residualGaloisRepOf` a two-dimensional residual representation over $\mathbb{Z}/p$ on $\operatorname{Tors}_p$; let $\rho$ be its base change along $\iota$ to $k$, regarded as a [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) over $k$ via `ofResidualGaloisRep`. The conclusion is `IsFlatAt p` for $\rho$: the residue field of $k$ is finite, and for every ideal $I \subseteq k$ with $k/I$ finite there is a commutative ring $H$ with a cocommutative Hopf algebra structure over the subring $\mathbb{Z}_{(p)} \subset \mathbb{Q}$ of rationals whose denominator is coprime to $p$, finite and flat as a module over that subring, together with a bijection $e$ from $\mathrm{Hom}_{\mathbb{Z}_{(p)}\text{-alg}}(H, \overline{\mathbb{Q}})$ (with its convolution product) onto $\rho.V/(I\cdot\rho.V)$ that turns convolution into addition and is equivariant: if $g = \sigma \circ f$ pointwise on $H$, then $e(g) = \rho.\mathrm{levelAction}\, I\, \sigma\, (e(f))$.
--
--   This is the statement that the mod $p$ representation attached to a Weierstrass curve which is semistable at $p$ and peu ramifiée at $p$ is flat at $p$, i.e. arises from a finite flat group scheme over $\mathbb{Z}_{(p)}$; the content for the multiplicative-reduction case is the Tate-curve criterion $p \mid v_p(\Delta)$, and for good reduction the $p$-torsion of the Néron model. It is the `IsFlatAt` packaging, over an arbitrary finite coefficient field $k$, used in the modularity-lifting input at $p$ downstream in the Hecke-algebra statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_semistable_of_isPeuRamifieeAt.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_WeierstrassCurve_PeuRamifiee

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_semistable_of_isPeuRamifieeAt
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Finite k]
    (ι : ZMod p →+* k) (hΔ : W.Δ ≠ 0)
    (hsemi : (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄)
    (hfin : (W.map (Int.castRingHom ℚ)).IsPeuRamifieeAt p p)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p)) :
    (GaloisRepAdic.ofResidualGaloisRep
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι)).IsFlatAt p := by sorry
