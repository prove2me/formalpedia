-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_theorem10
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.theorem10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:18:07.223985+00:00
-- url     : https://prove2.me/theorems/89ce7b50-44b2-46ff-92e5-378230da4ed8
-- title:
--   Theorem 10
-- statement:
--   Let $\mathcal E$ be the trace-preserving entanglement-breaking complex-linear qubit maps, and $\mathcal C$ the CQ maps. Then
--
--   $$\operatorname{Ext}(\mathcal E)\subseteq\mathcal C,\qquad\mathcal E=\operatorname{conv}_{\mathbb R}(\mathcal C).$$
--
--   These are both conclusions of the main theorem. It does not assert that every CQ map is extreme. The proof gap concerning intersecting planes on p.15 is recorded separately, without becoming a theorem hypothesis.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Theorem 10, PDF p. 14. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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















































































/-- Theorem 10, PDF pp.14-15: extreme-point inclusion and real convex-hull equality.
The plane-intersection proof gap is recorded, not assumed as a hypothesis. -/
theorem theorem10 : ebtSet.extremePoints ℝ ⊆ cqSet ∧ ebtSet = convexHull ℝ cqSet := by sorry






end QAlgorithms.Papers.Independent.Independent1.P08
