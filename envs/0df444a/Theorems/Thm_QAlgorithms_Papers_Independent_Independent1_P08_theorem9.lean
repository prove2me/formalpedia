-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_theorem9
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.theorem9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:16:54.046232+00:00
-- url     : https://prove2.me/theorems/dbad6062-d916-4f10-8ac3-490933a17032
-- title:
--   Theorem 9
-- statement:
--   Fix any translation $t\in\mathbb R^3$, and define $\Lambda_t=\{\lambda:\Phi_{t,\lambda}\text{ is completely positive}\}$. Then
--
--   $$\Lambda_t\cap(-\Lambda_t)=\{\lambda:\Phi_{t,\lambda}\text{ is EBT}\}.$$
--
--   Inversion negates $\lambda$ and leaves $t$ fixed. Infeasible translations are permitted; both sides can be empty.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Theorem 9, PDF p. 13. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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














































































/-- Theorem 9, PDF p.13: fixed translation, inversion of lambda alone. -/
theorem theorem9 (t : Bloch) :
    lambdaRegion t ∩ (fun lam : Bloch => -lam) ⁻¹' lambdaRegion t =
      {lam | EBT (canonical t lam)} := by sorry







end QAlgorithms.Papers.Independent.Independent1.P08
