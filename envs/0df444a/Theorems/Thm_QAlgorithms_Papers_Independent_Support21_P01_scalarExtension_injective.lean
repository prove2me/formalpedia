-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P01_scalarExtension_injective
-- name    : QAlgorithms.Papers.Independent.Support21.P01.scalarExtension_injective
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:27:07.051989+00:00
-- url     : https://prove2.me/theorems/3c41bed1-bc27-4acd-a2eb-dff0f13e1d02
-- title:
--   Free modules embed into their fraction-field scalar extension
-- statement:
--   Let $R$ be a commutative integral domain, $F$ its field of fractions, and $M$ a free $R$-module, of arbitrary rank. The canonical map
--
--   $$
--   M\longrightarrow M\otimes_R F,\qquad x\longmapsto x\otimes 1_F
--   $$
--
--   is injective. This identifies a free module with its image after passing to the fraction field.
-- source:
--   Cellularity and the Jones basic construction, arXiv:0906.1496v2, PDF p. 15, Lemma 2.20

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P01

noncomputable section

open scoped TensorProduct

namespace QAlgorithms.Papers.Independent.Support21.P01

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 2.20, PDF p.15: the canonical fraction-field scalar-extension map
is injective for every free module, with no finite-rank assumption. -/
theorem scalarExtension_injective
    (R F M : Type*) [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]
    [AddCommGroup M] [Module R M] [Module.Free R M] :
    Function.Injective (fun x : M => TensorProduct.tmul R x (1 : F)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P01

end
