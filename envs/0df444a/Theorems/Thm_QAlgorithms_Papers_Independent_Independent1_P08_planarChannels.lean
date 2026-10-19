-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_planarChannels
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.planarChannels
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:17:08.312234+00:00
-- url     : https://prove2.me/theorems/9340bfcd-e801-42d0-a9c4-54b6aeae1dbd
-- title:
--   Planar channels are entanglement breaking
-- statement:
--   Let $\Phi_{t,\lambda}$ be a CPT qubit map in canonical form. Then
--
--   $$\bigl(\exists j\in\{1,2,3\}:\lambda_j=0\bigr)\ \Longrightarrow\ \Phi_{t,\lambda}\text{ is entanglement breaking}.$$
--
--   The planar regime includes degenerate lines and points. This is a sufficient condition only.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Planar channels are entanglement breaking, PDF p. 11. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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









































































/-- Planar channels, PDF p.11: includes lines and points. -/
theorem planarChannels (t lam : Bloch) (hPhi : CPT (canonical t lam))
    (hzero : ∃ j, lam j = 0) : EBT (canonical t lam) := by sorry












end QAlgorithms.Papers.Independent.Independent1.P08
