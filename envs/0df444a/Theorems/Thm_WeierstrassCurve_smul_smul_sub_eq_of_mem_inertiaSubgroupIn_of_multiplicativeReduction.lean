-- Prove2me | Theorems.Thm_WeierstrassCurve_smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction
-- name    : WeierstrassCurve.smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/02f58cf5-9432-57bf-8d81-962d04d75a1b
-- title:
--   Inertia at multiplicative reduction acts unipotently on torsion
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $q$ be a prime number such that the discriminant $W.\Delta$ is nonzero, $q \mid W.\Delta$ and $q \nmid W.c_4$ (multiplicative reduction at $q$). Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime q`, i.e. the image of $q$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$, so that $A$ is a valuation ring above $q$. Let $n$ be a natural number with $q \nmid n$, and let $\sigma, \tau$ be $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ lying in `A.inertiaSubgroupIn ℚ`, the image in the full automorphism group of the inertia subgroup of $A$ under the inclusion of the decomposition subgroup of $A$ over $\mathbb{Q}$. Finally let $P$ be a point of the curve obtained from $W$ by base change along $\mathbb{Z} \to \mathbb{Q}$, taken with coordinates in $\overline{\mathbb{Q}}$, and assume $n \cdot P = 0$. Then $\tau \cdot (\sigma \cdot P - P) = \sigma \cdot P - P$; equivalently $(\tau - 1)(\sigma - 1)P = 0$ in the Galois module of $\overline{\mathbb{Q}}$-points.
--
--   This is the unipotence of the inertia action at a prime of multiplicative reduction on torsion of order prime to that prime, the group-theoretic input behind the Tate curve description of the local Galois representation. It is used in establishing that the Tate module representation is unipotent on inertia at such a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction.lean

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.smul_smul_sub_eq_of_mem_inertiaSubgroupIn_of_multiplicativeReduction
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0) (hqΔ : (q : ℤ) ∣ W.Δ)
    (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {n : ℕ} (hn : ¬ q ∣ n) {σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hP : n • P = 0) :
    τ • (σ • P - P) = σ • P - P := by sorry
