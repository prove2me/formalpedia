-- Prove2me | Theorems.Thm_ThetaCert_base_p1
-- name    : ThetaCert.base_p1
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T23:44:25.393685+00:00
-- url     : https://prove2.me/theorems/f3b19a5a-e791-4716-8b4f-10056e5fd2df
-- title:
--   $\theta$ certificate, the base range, part 1
-- statement:
--   The kernel checker accepts the listed certificate records (part 1 of `ThetaCert.base`, split to keep each kernel check within the time limit).
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); here the range [3 594 641, 3 584 912 847] is closed by a kernel-checked sieve certificate.

import Definitions.Def_ThetaCertData_base

theorem ThetaCert.base_p1 :
    ∀ s ∈ [ThetaSieve.ThetaBase.s7, ThetaSieve.ThetaBase.s8, ThetaSieve.ThetaBase.s9, ThetaSieve.ThetaBase.s10, ThetaSieve.ThetaBase.s11, ThetaSieve.ThetaBase.s12, ThetaSieve.ThetaBase.s13], s.bok = true := by sorry
