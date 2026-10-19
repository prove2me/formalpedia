-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_theorem3
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.theorem3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:16:12.993954+00:00
-- url     : https://prove2.me/theorems/4d672301-976c-4a4a-bbe3-86599584b905
-- title:
--   Theorem 3
-- statement:
--   Let $t,\lambda\in\mathbb R^3$, and let $\Phi_{t,\lambda}$ be the trace-preserving canonical Bloch map $v\mapsto t+\operatorname{diag}(\lambda)v$. If it is entanglement breaking, then
--
--   $$\sum_{j=1}^3|\lambda_j|\le1.$$
--
--   There is no unitality assumption. This is a necessary condition for the general translated channel.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Theorem 3, PDF p. 4. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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


































































/-- Theorem 3, PDF p.4: necessity also for nonunital maps. -/
theorem theorem3 (t lam : Bloch) (hPhi : EBT (canonical t lam)) :
    ∑ j, |lam j| ≤ 1 := by sorry



















end QAlgorithms.Papers.Independent.Independent1.P08
