-- Prove2me | Theorems.Thm_WeierstrassCurve_tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor
-- name    : WeierstrassCurve.tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/ced9024f-2556-55f3-9da3-b48d26fa63f1
-- title:
--   Tate module unramified at good primes q ≠ p
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $p$ be a prime. Assume the counting hypothesis `hcard`: for every $n$, the subgroup of elements killed by $p^{n}$ in the group of points of the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$, taken over $\overline{\mathbb{Q}}$ (realised as `AlgebraicClosure ℚ`), has cardinality $(p^{n})^{2}$. Let $q$ be a prime with $q \neq p$ such that $W$ is a good prime model at $q$ in the sense of `IsGoodPrimeFor`, i.e. $(q : \mathbb{Z})$ does not divide the discriminant $W.\Delta$ of the given integral model. The conclusion is that the $p$-adic Tate module representation `tateModuleRep` attached to $W_{\mathbb{Q}}$ and to `hcard` — the Galois module of sequences $(x_n)$ of $\overline{\mathbb{Q}}$-points with $p^{n} x_n = 0$ and $p\,x_{n+1} = x_n$, which `hcard` makes free of rank $2$ over $\mathbb{Z}_p$ with its adically continuous action of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ — is unramified at $q$ in the sense of [`GaloisRepAdic.IsUnramifiedAt`](def/GaloisRep_Adic.html#L37): for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, every element of the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $P$ over $\mathbb{Q}$ acts on the Tate module as the identity endomorphism.
--
--   This is the easy direction of the criterion of Néron–Ogg–Shafarevich for elliptic curves: good reduction at $q$ forces the $p$-adic Tate module to be inertially trivial at $q$ for $p \neq q$, here with the good-reduction hypothesis read off as non-divisibility of the discriminant of the given integral model by $q$. It supplies the "unramified outside $S$" clause in the deformation conditions imposed on the Tate module representation of a Frey curve, and is used in the verification of those conditions after base change and in the identification of the modular level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor.lean

import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor (W : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime]
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hgood : W.IsGoodPrimeFor q) :
    ((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).IsUnramifiedAt q := by sorry
