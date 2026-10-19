-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_tDecomposition
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.tDecomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:32:29.946155+00:00
-- url     : https://prove2.me/theorems/2df98130-853e-40a2-b6fb-aa1f10355542
-- title:
--   T decomposition and coefficient mass
-- statement:
--   Let $T=\operatorname{diag}(1,e^{i\pi/4})$ and $R_z=(I+iZ)/\sqrt2$ as in Table I. Write $[A](X)=AXA^\dagger$. Then, on every qubit operator,
--   $$[T]=\tfrac12[I]-\tfrac{\sqrt2-1}{2}[Z]
--    +\tfrac{\sqrt2}{2}[R_z^3],\qquad
--   \tfrac12+\left|\!-\tfrac{\sqrt2-1}{2}\right|+\tfrac{\sqrt2}{2}=\sqrt2.$$
--   Here $R_z^3$ implements $S$ up to global phase. This is an expectation-estimation decomposition, not deterministic synthesis with the corresponding time cost.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, §VII, T example, PDF p. 5. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
set_option autoImplicit false

/-! Endo, Benjamin and Li, arXiv:1712.09271v2; citations use PDF pages.
Source defects and construction deferrals are recorded in the assigned chunk. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P09

open ErrorMitigation















































/-- PDF p.5, §VII: T decomposition; Rz cubed is S up to phase, whereas Rz is S inverse. -/
theorem tDecomposition :
    (∀ X : Matrix Bool Bool ℂ,
      conjSuperop gateT X = ∑ i, (tCoefficients i : ℂ) • conjSuperop (tMatrices i) X) ∧
    coefficientMass tCoefficients = Real.sqrt 2 := by sorry
















end QAlgorithms.Papers.Independent.Independent1.P09
