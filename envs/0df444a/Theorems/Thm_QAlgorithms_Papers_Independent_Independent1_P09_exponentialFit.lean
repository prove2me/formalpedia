-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_exponentialFit
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.exponentialFit
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:32:46.293589+00:00
-- url     : https://prove2.me/theorems/2a7cbf46-ae36-4220-aa9f-f95692c9868d
-- title:
--   Conditional two-point exponential fit
-- statement:
--   Assume the exact model $z(e)=a\exp(-\kappa e)$ with $a>0$ and decay rate $\kappa>0$. Let $e_0>0$ and $r>1$. Its two positive model values recover the zero-error value exactly:
--   $$z(e_0)^{\,r/(r-1)}z(re_0)^{\,1/(1-r)}=a=z(0).$$
--   The positivity assumptions specify real powers. This is conditional on exponential decay to zero and exact model points; it makes no unbiasedness assertion about ratios of noisy empirical measurements and no universal decay claim for Markovian errors.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, §XI, pp.10–11, PDF p. 11. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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



























































/-- PDF pp.10–11, §XI: conditional exact exponential-model fit, not empirical ratio unbiasedness. -/
theorem exponentialFit (a decay e0 r : ℝ) (ha : 0 < a) (hdecay : 0 < decay)
    (he0 : 0 < e0) (hr : 1 < r) :
    (a*Real.exp (-decay*e0))^(r/(r-1)) *
      (a*Real.exp (-decay*(r*e0)))^(1/(1-r)) = a := by sorry




end QAlgorithms.Papers.Independent.Independent1.P09
