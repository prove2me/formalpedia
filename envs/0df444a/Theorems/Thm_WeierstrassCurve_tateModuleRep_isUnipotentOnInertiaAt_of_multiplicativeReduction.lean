-- Prove2me | Theorems.Thm_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction
-- name    : WeierstrassCurve.tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/76d4d620-74c1-5402-8f32-2c95856fd33e
-- title:
--   Unipotent inertia at a prime of multiplicative reduction
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $p$ be a prime. Assume the counting hypothesis `hcard`: for every $n$, the group of points of $W$ base changed to $\mathbb{Q}$ and then to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` that are killed by $p^n$ has cardinality $(p^n)^2$; this is what furnishes a free rank-two $\mathbb{Z}_p$-basis of the Tate module [`TateModule p`](def/EllipticCurve_TateModule.html#L15), the group of sequences $(x_n)$ of points with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, and hence the two-dimensional adically continuous Galois representation $\rho =$ `tateModuleRep` of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = (\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}})$ on it. Let $q$ be a prime with $q \neq p$, and assume $\Delta(W) \neq 0$, $q \mid \Delta(W)$ and $q \nmid c_4(W)$, i.e. the model is nonsingular over $\mathbb{Q}$ and has multiplicative reduction at $q$. The conclusion is `IsUnipotentOnInertiaAt q` for this representation: for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ over $\mathbb{Q}$, the characteristic polynomial of $\rho(\sigma)$ is $(X-1)^2$.
--
--   This is the elementary Tate-curve form of Grothendieck's description of inertia at a prime of semistable (here multiplicative) reduction: inertia at $q \neq p$ acts unipotently on the $p$-adic Tate module. It supplies the local condition at primes $q \in S$ with $q \neq p$ in the deformation problem attached to the Frey curve, and is used in the verification that the Galois representation of the curve satisfies the modularity hypotheses at the relevant level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction.lean

import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hΔ : W.Δ ≠ 0) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) :
    ((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).IsUnipotentOnInertiaAt q := by sorry
