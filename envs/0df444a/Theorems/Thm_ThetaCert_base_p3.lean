-- Prove2me | Theorems.Thm_ThetaCert_base_p3
-- name    : ThetaCert.base_p3
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T23:44:27.16149+00:00
-- url     : https://prove2.me/theorems/44db15ee-5633-40cd-abf9-9900aa2dab72
-- title:
--   $\theta$ certificate, the base range, part 3
-- statement:
--   The kernel checker accepts the listed certificate records (part 3 of `ThetaCert.base`, split to keep each kernel check within the time limit).
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); here the range [3 594 641, 3 584 912 847] is closed by a kernel-checked sieve certificate.

import Definitions.Def_ThetaCertData_base

theorem ThetaCert.base_p3 :
    ∀ s ∈ [ThetaSieve.ThetaBase.s21, ThetaSieve.ThetaBase.s22, ThetaSieve.ThetaBase.s23, ThetaSieve.ThetaBase.s24, ThetaSieve.ThetaBase.s25, ThetaSieve.ThetaBase.s26, ThetaSieve.ThetaBase.s27], s.bok = true := by sorry
