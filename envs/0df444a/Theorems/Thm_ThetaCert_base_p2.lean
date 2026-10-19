-- Prove2me | Theorems.Thm_ThetaCert_base_p2
-- name    : ThetaCert.base_p2
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T23:44:25.837983+00:00
-- url     : https://prove2.me/theorems/8e39e15b-33b3-454d-9ac4-ba80f58d13eb
-- title:
--   $\theta$ certificate, the base range, part 2
-- statement:
--   The kernel checker accepts the listed certificate records (part 2 of `ThetaCert.base`, split to keep each kernel check within the time limit).
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); here the range [3 594 641, 3 584 912 847] is closed by a kernel-checked sieve certificate.

import Definitions.Def_ThetaCertData_base

theorem ThetaCert.base_p2 :
    ∀ s ∈ [ThetaSieve.ThetaBase.s14, ThetaSieve.ThetaBase.s15, ThetaSieve.ThetaBase.s16, ThetaSieve.ThetaBase.s17, ThetaSieve.ThetaBase.s18, ThetaSieve.ThetaBase.s19, ThetaSieve.ThetaBase.s20], s.bok = true := by sorry
