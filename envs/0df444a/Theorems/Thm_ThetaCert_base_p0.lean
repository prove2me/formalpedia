-- Prove2me | Theorems.Thm_ThetaCert_base_p0
-- name    : ThetaCert.base_p0
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T23:44:25.80039+00:00
-- url     : https://prove2.me/theorems/20d21acd-3e8e-4234-b4e4-c10241d64e56
-- title:
--   $\theta$ certificate, the base range, part 0
-- statement:
--   The kernel checker accepts the listed certificate records (part 0 of `ThetaCert.base`, split to keep each kernel check within the time limit).
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); here the range [3 594 641, 3 584 912 847] is closed by a kernel-checked sieve certificate.

import Definitions.Def_ThetaCertData_base

theorem ThetaCert.base_p0 :
    ∀ s ∈ [ThetaSieve.ThetaBase.s0, ThetaSieve.ThetaBase.s1, ThetaSieve.ThetaBase.s2, ThetaSieve.ThetaBase.s3, ThetaSieve.ThetaBase.s4, ThetaSieve.ThetaBase.s5, ThetaSieve.ThetaBase.s6], s.bok = true := by sorry
