-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_unitalConvexHull
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.unitalConvexHull
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:17:11.751991+00:00
-- url     : https://prove2.me/theorems/7dc2c8a8-4d28-4078-8ae3-93de24c72936
-- title:
--   Unital EBT channels are the convex hull of unital CQ maps
-- statement:
--   In the real vector space of complex-linear qubit maps, let $\mathcal E_u$ be the unital trace-preserving entanglement-breaking maps, and $\mathcal C_u$ the unital CQ maps. Then
--
--   $$\mathcal E_u=\operatorname{conv}_{\mathbb R}(\mathcal C_u).$$
--
--   The channel sets allow arbitrary input and output bases. This is a statement in map space, not only in one diagonal parameter slice.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Unital EBT channels are the convex hull of unital CQ maps, PDF p. 12. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
set_option autoImplicit false

/-! Ruskai, Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3.
All locators are PDF pages. Convexity is real; ambiguous claims are in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P08

open QAlgorithms.Entanglement QAlgorithms.QubitChannels













































































/-- Theorem 8, Remark 1, PDF p.12: map-space convex hull, all bases. -/
theorem unitalConvexHull : {Phi : QMap | EBT Phi ∧ Phi 1 = 1} =
    convexHull ℝ {Phi : QMap | IsCQMap Phi ∧ Phi 1 = 1} := by sorry








end QAlgorithms.Papers.Independent.Independent1.P08
