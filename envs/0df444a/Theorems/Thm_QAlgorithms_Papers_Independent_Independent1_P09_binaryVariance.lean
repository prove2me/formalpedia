-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_binaryVariance
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.binaryVariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:26:18.455128+00:00
-- url     : https://prove2.me/theorems/134a6efc-d668-4cdc-854e-451a1e216386
-- title:
--   Binary variance and exact sample overhead
-- statement:
--   Let $Y$ take values $+1,-1$ with probabilities $p,1-p$, where $0\le p\le1$. Let $C>0$, $m=C(2p-1)$ and $|m|\le1$. For independent trials $Y_1,\ldots,Y_R$, with integers $R,R_0\ge1$, let $\widehat m=C R^{-1}\sum_iY_i$. Then
--   $$\mathbb E[(\widehat m-m)^2]=\frac{C^2-m^2}{R},\qquad
--   \sqrt{\mathbb E[(\widehat m-m)^2]}\le\frac C{\sqrt R}.$$
--   If $|m|<1$, equality of this variance with the ideal binary-sampling variance $(1-m^2)/R_0$ holds exactly when
--   $$\frac R{R_0}=\frac{C^2-m^2}{1-m^2}.$$
--   The model has no postselection zeros. The formula distinguishes the exact overhead ratio from the usual $C^2$ approximation; any desired positive standard deviation can be met using the displayed upper bound.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, §VI, PDF p. 4. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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












































/-- PDF p.4, §VI: binary variance and exact sample overhead; deterministic ideal outputs excluded. -/
theorem binaryVariance (p C : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hC : 0 < C)
    (R R0 : ℕ) (hR : 0 < R) (hR0 : 0 < R0)
    (idealRange : |C*(2*p-1)| ≤ 1) :
    let weight : Bool → ℝ := fun b => if b then p else 1-p
    let value : Bool → ℝ := fun b => if b then 1 else -1
    let m := C*(2*p-1)
    let mean : (Fin R → Bool) → ℝ := fun z => C/(R : ℝ)*∑ i, value (z i)
    (∑ z : Fin R → Bool, (∏ i, weight (z i)) * (mean z-m)^2) =
      (C^2-m^2)/(R : ℝ) ∧
    Real.sqrt ((C^2-m^2)/(R : ℝ)) ≤ C/Real.sqrt R ∧
    (|m| < 1 →
      (((C^2-m^2)/(R : ℝ) = (1-m^2)/(R0 : ℝ)) ↔
        (R : ℝ)/(R0 : ℝ) = (C^2-m^2)/(1-m^2))) := by sorry



















end QAlgorithms.Papers.Independent.Independent1.P09
