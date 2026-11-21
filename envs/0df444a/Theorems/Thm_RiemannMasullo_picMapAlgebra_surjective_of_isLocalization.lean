-- Prove2me | Theorems.Thm_RiemannMasullo_picMapAlgebra_surjective_of_isLocalization
-- name    : RiemannMasullo.picMapAlgebra_surjective_of_isLocalization
-- status  : Proved
-- author  : @koffie
-- created : 2026-11-20T23:07:32.81502+00:00
-- url     : https://prove2.me/theorems/d9565778-efe6-40f9-ae11-6eacaca7b741
-- title:
--   Picard groups of Dedekind domains surject onto those of their localizations
-- statement:
--   Let $R$ be a Dedekind domain, $M\subseteq R$ a multiplicative submonoid, and $A=M^{-1}R$ a localization of $R$ at $M$ that is again a Dedekind domain. Then the base-change map on Picard groups
--
--   $$\operatorname{Pic}(R)\longrightarrow\operatorname{Pic}(A),\qquad [P]\longmapsto[A\otimes_R P],$$
--
--   is surjective.
--
--   For Dedekind domains the Picard group is the ideal class group. The statement says that every ideal class of the localization comes from an ideal class of $R$. Masullo uses it in Appendix A, eq. (A.1.5.9), p. 544, to compare the class groups of $\mathcal O_F$ and of the rings of $S$-integers $\mathcal O_{F,S}$.
--
--   **Formalization Note** `CommRing.Pic.mapAlgebra R A` is Mathlib's base-change homomorphism of Picard groups.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/9d5c8b94a1f1b5d8f903f1b04d1e043877e7bb15/RiemannMasullo/ForMathlib/RingTheory/PicardGroup.lean#L44-L71 (R. McCorvie et al., riemann-masullo, Apache-2.0); used for A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix A, eq. (A.1.5.9), p. 544.

import Mathlib

namespace RiemannMasullo

theorem picMapAlgebra_surjective_of_isLocalization {R : Type*} [CommRing R] [IsDedekindDomain R]
    (M : Submonoid R) (A : Type*) [CommRing A] [IsDedekindDomain A] [Algebra R A]
    [IsLocalization M A] : Function.Surjective (CommRing.Pic.mapAlgebra R A) := by sorry

end RiemannMasullo
