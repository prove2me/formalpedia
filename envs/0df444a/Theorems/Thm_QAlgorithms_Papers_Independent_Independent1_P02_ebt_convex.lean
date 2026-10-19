-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_ebt_convex
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.ebt_convex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:17:54.763606+00:00
-- url     : https://prove2.me/theorems/3040fe77-8ef8-42e1-8530-f182b9857491
-- title:
--   Theorem 3: convexity of EBT
-- statement:
--   For $d\ge1$, let $\mathrm{EBT}_d$ be the set of complex-linear entanglement-breaking, trace-preserving maps on $M_d(\mathbb C)$. Then
--
--   $$\mathrm{EBT}_d\text{ is convex over }\mathbb R.$$
--
--   Thus $a\Phi+(1-a)\Psi$ is EBT for any two EBT maps and any $a\in[0,1]$. Convexity refers to maps on all operators and supports the paper's study of extreme channels.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Theorem 3: convexity of EBT, PDF p. 3. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02



















































/-- Theorem 3, PDF p.3: convexity in the real vector space of complex-linear maps. -/
theorem ebt_convex (d : ℕ) (hd : 0 < d) : Convex ℝ (ebtSet d) := by sorry


















end QAlgorithms.Papers.Independent.Independent1.P02
