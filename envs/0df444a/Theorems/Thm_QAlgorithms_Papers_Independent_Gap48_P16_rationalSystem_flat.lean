-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_rationalSystem_flat
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.rationalSystem_flat
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:51:56.0699+00:00
-- url     : https://prove2.me/theorems/3e901316-f0f9-4a86-9c3e-0c74d81522d9
-- title:
--   Remark 2.4: flatness of rational systems
-- statement:
--   Let $R$ be a commutative unital ring and let $b:P\times A\to R$ be a bilinear pairing of arbitrary $R$-modules. Suppose the system is rational: for every $R$-module $X$, the map $\alpha_X(x\otimes p)(a)=b(p,a)x$ is injective. Then
--
--   $$P\text{ is flat over }R.$$
--
--   This gives the exact tensor-inclusion property needed for rational systems; projectivity and noetherianness are not assumed.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 4, Remark 2.4: flatness of rational systems

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Pairings

variable {R A P Q B M : Type u} [CommRing R]

variable [AddCommGroup A] [Module R A] [AddCommGroup P] [Module R P]

variable [AddCommGroup Q] [Module R Q] [AddCommGroup B] [Module R B]

variable [AddCommGroup M] [Module R M]

/-- Remark 2.4, PDF p.4: rational systems have flat first module. -/
theorem rationalSystem_flat (b : P →ₗ[R] A →ₗ[R] R) (h : IsRationalSystem b) :
    Module.Flat R P := by sorry

end Pairings

end QAlgorithms.Papers.Independent.Gap48.P16

end
