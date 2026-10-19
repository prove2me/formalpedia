-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_pauliErrorComponent
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.pauliErrorComponent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:33:34.090555+00:00
-- url     : https://prove2.me/theorems/e5f3dbd7-2920-4de2-a646-d60c063e251d
-- title:
--   Fixed-ratio Pauli error component
-- statement:
--   Let $w_x,w_y,w_z\ge0$ sum to one and let $0<\epsilon\le1$. Set $p_\alpha=\epsilon w_\alpha$ and $\mathcal E'=\sum_{\alpha=x,y,z}w_\alpha[\sigma_\alpha]$. Then
--   $$\epsilon^{-1}\sum_\alpha p_\alpha[\sigma_\alpha]=\mathcal E',\qquad
--   (1-\epsilon)\operatorname{id}+\sum_\alpha p_\alpha[\sigma_\alpha]
--   =(1-\epsilon)\operatorname{id}+\epsilon\mathcal E'.$$
--   The component $\mathcal E'$ is independent of $\epsilon$ because the ratios are fixed. The identities hold on all input operators and avoid division by zero.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, Appendix J, PDF p. 19. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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





























































/-- PDF p.19, Appendix J: fixed relative Pauli weights give an epsilon-independent component. -/
theorem pauliErrorComponent (weights : Fin 3 → ℝ)
    (nonnegative : ∀ j, 0 ≤ weights j) (total : ∑ j, weights j = 1)
    (eps : ℝ) (heps : 0 < eps ∧ eps ≤ 1) :
    let sigma : Fin 3 → Matrix Bool Bool ℂ := ![pauliX,pauliY,pauliZ]
    let component := ∑ j, weights j • krausLinearMap (fun _ : Fin 1 => sigma j)
    (eps⁻¹ : ℝ) • (∑ j, (eps*weights j) • krausLinearMap (fun _ : Fin 1 => sigma j)) = component ∧
    ∀ X, (1-eps : ℂ) • X +
      (∑ j, ((eps*weights j : ℝ) : ℂ) • conjSuperop (sigma j) X) =
        (1-eps : ℂ) • X + (eps : ℂ) • component X := by sorry


end QAlgorithms.Papers.Independent.Independent1.P09
