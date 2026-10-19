-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_parallelogramSameBasis
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.parallelogramSameBasis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:18:15.632767+00:00
-- url     : https://prove2.me/theorems/7d282513-aaf1-4753-aaaa-cfd47cb2b1ca
-- title:
--   Remark c parallelogram of same-basis decompositions
-- statement:
--   Fix $t\in\mathbb R^3$ and $l_3\in\mathbb R$. Let $P$ consist of canonical EBT maps with these fixed parameters and either $\lambda_1=0$ or $\lambda_2=0$. Let $\mathcal C_{\rm diag}$ be all CQ maps canonical in the same basis. Then
--
--   $$\operatorname{conv}_{\mathbb R}(P)\subseteq\operatorname{conv}_{\mathbb R}(\mathcal C_{\rm diag}).$$
--
--   This gives the same-basis decomposition on the illustrated parallelogram. It neither covers the entire slice nor requires CQ summands to retain $l_3$.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Remark c parallelogram of same-basis decompositions, PDF p. 17. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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



















































































/-- Remark (c), PDF p.17: only hull of planar slice points; no fixed lambda3 for summands. -/
theorem parallelogramSameBasis (t : Bloch) (l3 : ℝ) :
    convexHull ℝ (planarSliceMaps t l3) ⊆ convexHull ℝ canonicalCQ := by sorry


end QAlgorithms.Papers.Independent.Independent1.P08
