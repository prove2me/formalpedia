-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_spamStability
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.spamStability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:28:19.598541+00:00
-- url     : https://prove2.me/theorems/04183931-ec3a-4bd4-b283-bcce6477aa40
-- title:
--   Symbolic SPAM stability
-- statement:
--   Let $M_{{\rm in},j},M_{{\rm out},j}$ be invertible real local tomography frames on $n$ wires. Use the reference matrices $M_{\rm in}^0,M_{\rm out}^0$ computed from the Appendix D preparations and observables. Let $e_{\rm in}=\max_j\|M_{{\rm in},j}-M_{\rm in}^0\|_2$ and $e_{\rm out}=\max_j\|M_{{\rm out},j}-M_{\rm out}^0\|_2$. For the choice $T_j=M_{\rm in}^0$, the estimated input frame is exactly $M_{\rm in}^0$, so its error is zero. The estimated output frames are $M_{{\rm out},j}M_{{\rm in},j}(M_{\rm in}^0)^{-1}$ and satisfy
--   $$\widehat e_{\rm out}\le
--   (e_{\rm out}e_{\rm in}+\|M_{\rm in}^0\|_2e_{\rm out}
--   +\|M_{\rm out}^0\|_2e_{\rm in})\|(M_{\rm in}^0)^{-1}\|_2.$$
--   The empty-wire maxima are zero. This keeps the valid symbolic bound separate from the printed numerical norm evaluations.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, Appendix F (F1)–(F6), PDF p. 15. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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
























































/-- PDF pp.14–15, (F1)–(F6): symbolic SPAM stability for T=Min0. -/
theorem spamStability {n : ℕ}
    (Min Mout : Fin n → Matrix (Fin 4) (Fin 4) ℝ)
    (hin : ∀ j, IsUnit (Min j)) (hout : ∀ j, IsUnit (Mout j)) :
    let ein := maxLocalError Min referenceInput
    let eout := maxLocalError Mout referenceOutput
    maxLocalError (fun _ : Fin n => referenceInput) referenceInput = 0 ∧
    maxLocalError (fun j => Mout j*Min j*referenceInput⁻¹) referenceOutput ≤
      (eout*ein + specNorm referenceInput*eout + specNorm referenceOutput*ein)*
        specNorm referenceInput⁻¹ := by sorry







end QAlgorithms.Papers.Independent.Independent1.P09
