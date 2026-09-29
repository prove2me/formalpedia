-- Prove2me | Theorems.Thm_WeierstrassCurve_smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd
-- name    : WeierstrassCurve.smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/0f26d1b7-cd40-5cba-b679-2aeed703a6c5
-- title:
--   Inertia fixes ℓ-torsion off the zero component when ℓ∣ v_q(Δ)
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$ and let $q,\ell$ be primes with $\ell\neq q$. Assume $W.\Delta\neq 0$, that $q\mid W.\Delta$ and $q\nmid W.c_4$ in $\mathbb Z$, and that $\ell$ divides $\mathrm{padicValInt}\,q\,(W.\Delta)$. Let $A$ be a valuation subring of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` lying over $q$ in the sense that the image of $q$ lies in the non-units of $A$. Assume further that every element of the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ over $\mathbb Q$ fixes every point $P$ of $W$ base changed to $\overline{\mathbb Q}$ with $\ell\cdot P=0$ satisfying `W.InZeroComponentAt A P`, that is, with $P=0$ or $P=(x,y)$ such that either $x\notin A$, or $x,y\in A$ and the residues of $x,y$ in the residue field of $A$ form a nonsingular point of the reduced Weierstrass curve. Then for every $\sigma$ in that image of inertia and every point $P$ with $\ell\cdot P=0$ for which `W.InZeroComponentAt A P` fails, one has $\sigma\cdot P=P$.
--
--   This is the half of the criterion "$\ell\mid v_q(\Delta)$ at a prime $q\neq\ell$ of multiplicative reduction implies that $E[\ell]$ is unramified at $q$" which concerns the $\ell$-torsion points reducing to the node, classically read off the Tate parametrisation; it is the step used for the Frey curve at the odd primes dividing $abc$. It is cited by [`WeierstrassCurve.galoisRepUnramifiedAt_of_multiplicativeReduction`](thm.html#WeierstrassCurve.galoisRepUnramifiedAt_of_multiplicativeReduction).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd
    (W : WeierstrassCurve ℤ) {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hv : ℓ ∣ padicValInt q W.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hM : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      ∀ P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, ℓ • P = 0 →
        W.InZeroComponentAt A P → σ • P = P)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hP : ℓ • P = 0)
    (hnot : ¬ W.InZeroComponentAt A P) :
    σ • P = P := by sorry
