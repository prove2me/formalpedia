-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_theorem2
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.theorem2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:16:15.019889+00:00
-- url     : https://prove2.me/theorems/0bb9487a-a288-4bd5-a0fe-ce123537edea
-- title:
--   Theorem 2
-- statement:
--   Let $\Phi:M_2(\mathbb C)\to M_2(\mathbb C)$ be complex-linear, completely positive and trace preserving. Let $|\beta\rangle=(|00\rangle+|11\rangle)/\sqrt2$ and $\Gamma_\Phi=(\mathrm{id}\otimes\Phi)(|\beta\rangle\langle\beta|)$. Then
--
--   $$\Phi\text{ is entanglement breaking}\quad\Longleftrightarrow\quad \Gamma_\Phi\le\tfrac12 I_4.$$
--
--   The inequality is the positive-semidefinite operator order. This provides an operator test on the normalized Choi state.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Theorem 2, PDF p. 4. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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

































































/-- Theorem 2, PDF p.4: normalized Choi-state operator inequality. -/
theorem theorem2 (Phi : QMap) (hPhi : CPT Phi) :
    EBT Phi ↔ ((1/2 : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)-choiState Phi).PosSemidef := by sorry




















end QAlgorithms.Papers.Independent.Independent1.P08
