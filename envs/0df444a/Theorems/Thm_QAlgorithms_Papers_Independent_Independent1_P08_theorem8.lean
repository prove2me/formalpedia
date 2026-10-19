-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_theorem8
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.theorem8
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:17:05.291145+00:00
-- url     : https://prove2.me/theorems/85f9046b-24db-4087-8ffe-df28d22fa69a
-- title:
--   Theorem 8
-- statement:
--   In a fixed diagonal basis, let $\mathcal U=\{\lambda\in\mathbb R^3:\Phi_{0,\lambda}\text{ is CPT and EBT}\}$, and $V=\{\pm e_1,\pm e_2,\pm e_3\}$. Then
--
--   $$\mathcal U=\operatorname{conv}_{\mathbb R}(V),\qquad\operatorname{Ext}(\mathcal U)=V.$$
--
--   The theorem determines both the entire parameter octahedron and exactly its six extreme points.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Theorem 8, PDF p. 12. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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












































































/-- Theorem 8, PDF p.12: whole octahedron and exact six extreme points. -/
theorem theorem8 : unitalParameters = convexHull ℝ octahedronVertices ∧
    unitalParameters.extremePoints ℝ = octahedronVertices := by sorry









end QAlgorithms.Papers.Independent.Independent1.P08
