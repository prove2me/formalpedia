-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_theorem4
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.theorem4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:15:49.304815+00:00
-- url     : https://prove2.me/theorems/8d7403ef-2661-45d0-8264-41839962e511
-- title:
--   Theorem 4
-- statement:
--   Let $\Phi$ be a completely positive trace-preserving qubit map with $\Phi(I)=I$. Suppose independent unitary changes of input and output bases put it in canonical form with parameters $t,\lambda\in\mathbb R^3$. Then
--
--   $$\Phi\text{ is entanglement breaking}\quad\Longleftrightarrow\quad\sum_{j=1}^3|\lambda_j|\le1.$$
--
--   This makes the necessary condition sufficient in the unital case.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Theorem 4, PDF p. 4. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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



































































/-- Theorem 4, PDF p.4: CPT, unitality and a chosen canonical representation. -/
theorem theorem4 (Phi : QMap) (hPhi : CPT Phi) (hunital : Phi 1 = 1)
    (t lam : Bloch) (hcanonical : HasCanonicalRepresentation Phi t lam) :
    EBT Phi ↔ ∑ j, |lam j| ≤ 1 := by sorry


















end QAlgorithms.Papers.Independent.Independent1.P08
