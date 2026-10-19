-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_extremePOVMNonextremeChannel
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.extremePOVMNonextremeChannel
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:17:04.043042+00:00
-- url     : https://prove2.me/theorems/4a3b7ed8-0b88-4b78-933c-59b6c053597c
-- title:
--   Extreme POVM need not give an extreme channel
-- statement:
--   Set $w^1=(1,0,0)$, $w^2=(-1/2,0,\sqrt3/2)$, $w^3=(-1/2,0,-\sqrt3/2)$, and $E_k=(I+w^k\cdot\sigma)/3$. Set $R_k=(I+\sigma_k)/2$, with $\sigma_1=X,\sigma_2=Y,\sigma_3=Z$, and define
--
--   $$\Phi(X)=\sum_{k=1}^3\operatorname{Tr}(E_kX)R_k.$$
--
--   The effects form an extreme three-outcome POVM, each $R_k$ is a density matrix, and $\Phi$ is EBT, neither CQ nor a point channel, and not extreme in the EBT set. Thus extreme measurement data need not produce an extreme channel.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Extreme POVM need not give an extreme channel, PDF p. 7. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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







































































/-- Explicit extreme-POVM/nonextreme-channel example, PDF p.7. -/
theorem extremePOVMNonextremeChannel :
    trineEffect ∈ ({F : Fin 3 → Matrix Bool Bool ℂ | IsPOVM F}).extremePoints ℝ ∧
    (∀ k, IsDensityMatrix (trineOutput k)) ∧ EBT trineChannel ∧
    ¬ IsCQMap trineChannel ∧ ¬ IsPoint trineChannel ∧
    trineChannel ∉ ebtSet.extremePoints ℝ := by sorry














end QAlgorithms.Papers.Independent.Independent1.P08
