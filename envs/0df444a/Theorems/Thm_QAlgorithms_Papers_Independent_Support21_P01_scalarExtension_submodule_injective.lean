-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P01_scalarExtension_submodule_injective
-- name    : QAlgorithms.Papers.Independent.Support21.P01.scalarExtension_submodule_injective
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:27:35.109278+00:00
-- url     : https://prove2.me/theorems/cc75bf6b-0354-46be-9c20-9104a159ff60
-- title:
--   Scalar extension preserves a submodule inclusion into a free module
-- statement:
--   Let $R$ be a commutative integral domain with fraction field $F$. Let $N_2$ be a free $R$-module and let $N_1\subseteq N_2$ be an $R$-submodule, with inclusion $\iota$. Then
--
--   $$
--   \iota\otimes\operatorname{id}_F:N_1\otimes_R F\longrightarrow N_2\otimes_R F
--   $$
--
--   is injective. Neither module is required to have finite rank, and freeness is assumed only for $N_2$. This allows submodule filtrations to be regarded as filtrations after extending scalars.
-- source:
--   Cellularity and the Jones basic construction, arXiv:0906.1496v2, PDF p. 15, Lemma 2.21

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P01

noncomputable section

open scoped TensorProduct

namespace QAlgorithms.Papers.Independent.Support21.P01

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 2.21, PDF p.15: tensor the actual submodule inclusion with id_F.
Only the ambient module N2 is assumed free; N1 need not be free or finite. -/
theorem scalarExtension_submodule_injective
    (R F N2 : Type*) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]
    [AddCommGroup N2] [Module R N2] [Module.Free R N2]
    (N1 : Submodule R N2) :
    Function.Injective
      (TensorProduct.map N1.subtype (LinearMap.id : F →ₗ[R] F)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P01

end
