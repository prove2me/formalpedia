-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_prime_isGoodPrimeFor_dvd_apOfModel_dvd_add_one
-- name    : WeierstrassCurve.exists_prime_isGoodPrimeFor_dvd_apOfModel_dvd_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/cd143412-fb90-55da-b480-8f067143e395
-- title:
--   Auxiliary primes with p ∣ a_{q'} and p ∣ q'+1
-- statement:
--   Let $W$ be a Weierstrass equation over $\mathbb{Z}$ whose discriminant satisfies $W.\Delta \neq 0$, let $p$ be a prime, and let $S$ be a finite set of natural numbers. Then there exists a prime $q'$ with $q' \notin S$ such that: $q'$ is a good prime for $W$ in the sense that $q'$, viewed in $\mathbb{Z}$, does not divide $W.\Delta$; the integer $p$ divides $W.\mathrm{apOfModel}\,q'$, which is by definition the trace of Frobenius $q' + 1 - \#\,\widetilde{W}$ of the Weierstrass curve $\widetilde{W}$ over $\mathbb{Z}/q'\mathbb{Z}$ obtained from $W$ by applying the canonical ring homomorphism $\mathbb{Z} \to \mathbb{Z}/q'\mathbb{Z}$ to the coefficients (here $\#\,\widetilde{W}$ is the cardinality attached to that curve and $q' = \#(\mathbb{Z}/q'\mathbb{Z})$); and $p$ divides $q' + 1$ in $\mathbb{Z}$. Thus infinitely many such primes exist, since $S$ is arbitrary.
--
--   This produces the auxiliary primes used in Ribet's level-lowering argument: primes $q'$ of good reduction, avoiding any prescribed finite set, at which the trace of Frobenius is $\equiv 0$ and $q' \equiv -1 \pmod p$, so that the mod $p$ representation looks at $q'$ as it does at complex conjugation. It is used in the proof of [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_prime_isGoodPrimeFor_dvd_apOfModel_dvd_add_one.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_prime_isGoodPrimeFor_dvd_apOfModel_dvd_add_one
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (p : ℕ) (hp : p.Prime) (S : Finset ℕ) :
    ∃ q' : ℕ, q'.Prime ∧ q' ∉ S ∧ W.IsGoodPrimeFor q' ∧
      (p : ℤ) ∣ W.apOfModel q' ∧ (p : ℤ) ∣ (q' : ℤ) + 1 := by sorry
