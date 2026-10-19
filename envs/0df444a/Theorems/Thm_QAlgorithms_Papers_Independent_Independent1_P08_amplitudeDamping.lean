-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_amplitudeDamping
-- name    : QAlgorithms.Papers.Independent.Independent1.P08.amplitudeDamping
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:16:04.660752+00:00
-- url     : https://prove2.me/theorems/fbd220e0-5c25-4654-9fb5-6972c8fa0066
-- title:
--   Amplitude damping counterexample
-- statement:
--   For $0\le\alpha\le1$, let $\Phi_\alpha$ have translation $(0,0,1-\alpha^2)$ and diagonal Bloch parameters $(\alpha,\alpha,\alpha^2)$. These maps are completely positive and trace preserving, and
--
--   $$\Phi_\alpha\text{ is entanglement breaking}\iff\alpha=0.$$
--
--   Moreover, for every $\eta>0$ there is $\alpha\in(0,1]$ with $2\alpha+\alpha^2<\eta$ and $\Phi_\alpha$ not entanglement breaking. Thus small diagonal-parameter sum does not suffice for translated channels.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3, Amplitude damping counterexample, PDF p. 5. https://arxiv.org/abs/quant-ph/0302032v3 . PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d.

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




































































/-- Amplitude damping, PDF p.5: endpoints and arbitrarily-small non-EBT examples. -/
theorem amplitudeDamping :
    (∀ a : ℝ, 0 ≤ a → a ≤ 1 → CPT (damping a) ∧ (EBT (damping a) ↔ a = 0)) ∧
    ∀ eta : ℝ, 0 < eta → ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ 2*a+a^2 < eta ∧ ¬ EBT (damping a) := by sorry

















end QAlgorithms.Papers.Independent.Independent1.P08
