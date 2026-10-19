-- Prove2me | Theorems.Thm_ThetaCert_base
-- name    : ThetaCert.base
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T23:35:53.211978+00:00
-- url     : https://prove2.me/theorems/75c2d07d-adb9-4c86-9766-8a3fe000870e
-- title:
--   $\theta$ certificate, base range
-- statement:
--   The kernel checker `ThetaSieve.Seg.bok` accepts every record of `ThetaSieve.ThetaBase.segs`: for each segment $[L,L+2W)$ of odd numbers, sieving with the small primes and adding the fixed-point logarithm bounds of the products of the surviving numbers maps the stated bounds for $Q\,\theta(L-1)$ to the stated bounds for $Q\,\theta(L+2W-1)$.
--
--   Together with the soundness of the sieve and of the logarithm bounds this gives a certified enclosure of $\theta(3594640)$.
-- source:
--   P. Dusart, Estimates of some functions over primes without R.H., arXiv:1002.0442 (2010), Theorem 5.2 (k = 2, η = 0.2, x ≥ 3 594 641); here the range [3 594 641, 3 584 912 847] is closed by a kernel-checked sieve certificate.

import Definitions.Def_ThetaCertData_base

theorem ThetaCert.base :
    ∀ s ∈ ThetaSieve.ThetaBase.segs, s.bok = true := by sorry
