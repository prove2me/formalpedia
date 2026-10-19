-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_spamCoordinates
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.spamCoordinates
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:26:45.076188+00:00
-- url     : https://prove2.me/theorems/4a1d4d24-f642-4028-92a3-8363ec11d6d9
-- title:
--   SPAM reference frames and coordinates
-- statement:
--   Use reference preparations $|0\rangle,|1\rangle,|+\rangle,|y+\rangle$ and reference observables $I,X,Y,Z$. Let $M_{\rm in}^0$ have entries $\operatorname{Tr}(\sigma_a\rho_i^0)$, and let $M_{\rm out}^0$ have entries $\tfrac12\operatorname{Tr}(\sigma_a Q_i^0)$, in Pauli order. For physical density preparations $\rho_i$ and Hermitian observables $Q_i$, form $M_{\rm in},M_{\rm out}$ with the same formulas. The reference frames are invertible. With $\|\cdot\|_{\max}$ denoting largest absolute entry,
--   $$\|M_\alpha-M_\alpha^0\|_{\max}<\tfrac14s_{\min}(M_\alpha^0)
--   \ \Longrightarrow\ M_\alpha\text{ is invertible}\quad(\alpha={\rm in,out}).$$
--   Whenever $M_{\rm in}$ is invertible, every column $v$ has unique coordinates $q=M_{\rm in}^{-1}v$. Whenever $M_{\rm out}$ is invertible, every row $w$ has unique coordinates $q=wM_{\rm out}^{-1}$. Multiplication by the respective frame reconstructs the target exactly. These statements include all complete frames, not only nearby ones.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, Appendix D, pp.13–14, PDF p. 13. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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



















































/-- PDF pp.13–14, Appendix D: reference SPAM frames, perturbation domains, computed coordinates. -/
theorem spamCoordinates
    (rho : Fin 4 → Matrix Bool Bool ℂ) (density : ∀ i, IsDensityMatrix (rho i))
    (Q : Fin 4 → Matrix Bool Bool ℂ) (hermitian : ∀ i, (Q i).IsHermitian) :
    let Min := Matrix.of fun a i => ((pauliOrder a).mat*rho i).trace.re
    let Mout := Matrix.of fun i a => (2⁻¹ : ℝ)*((pauliOrder a).mat*Q i).trace.re
    IsUnit referenceInput ∧ IsUnit referenceOutput ∧
    (entryMax (Min-referenceInput) < leastSingular (by omega) referenceInput/4 → IsUnit Min) ∧
    (entryMax (Mout-referenceOutput) < leastSingular (by omega) referenceOutput/4 → IsUnit Mout) ∧
    (IsUnit Min →
      (∀ v : Fin 4 → ℝ, ∃! q : Fin 4 → ℝ, Min.mulVec q = v) ∧
      (∀ v : Fin 4 → ℝ, Min.mulVec (Min⁻¹.mulVec v) = v)) ∧
    (IsUnit Mout →
      (∀ v : Fin 4 → ℝ, ∃! q : Fin 4 → ℝ, Matrix.vecMul q Mout = v) ∧
      (∀ v : Fin 4 → ℝ, Matrix.vecMul (Matrix.vecMul v Mout⁻¹) Mout = v)) := by sorry












end QAlgorithms.Papers.Independent.Independent1.P09
