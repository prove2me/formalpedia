-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_leakageErrorComponent
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.leakageErrorComponent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:32:36.232447+00:00
-- url     : https://prove2.me/theorems/ae8db9d3-4232-4143-83ed-865fd21780d8
-- title:
--   Leakage component and one-sided expansion
-- statement:
--   Let $\pi_0=|0\rangle\langle0|$, $\pi_1=|1\rangle\langle1|$ and $\mathcal L_p=[\pi_0+\sqrt{1-p}\,\pi_1]$. For $0<p\le1$, define $c(p)=(\sqrt{1-p}-(1-p))/p$ and
--   $$\mathcal E'_p(X)=\pi_0X\pi_0+c(p)(\pi_0X\pi_1+\pi_1X\pi_0).$$
--   For every qubit operator $X$,
--   $$\mathcal L_p(X)=(1-p)X+p\mathcal E'_p(X).$$
--   Moreover $c(p)\to\tfrac12$ as $p\downarrow0$ and $c(p)-\tfrac12=O(p)$ on the punctured positive neighborhood of zero, with uniform constants on that neighborhood. This describes slow variation of a trace-decreasing model's component, not exact exponential decay of all expectations.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, Appendix J (J1); §XI p.9, PDF p. 19. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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






























































/-- PDF pp.9,19, (J1): leakage identity and punctured one-sided expansion; zero is not the limit. -/
theorem leakageErrorComponent :
    (∀ p : ℝ, 0 < p → p ≤ 1 → ∀ X : Matrix Bool Bool ℂ,
      leakageMap p X = (1-p : ℂ) • X + (p : ℂ) • leakageComponent p X) ∧
    Filter.Tendsto leakageFactor (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1/2 : ℝ)) ∧
    Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun p => leakageFactor p-1/2) (fun p : ℝ => p) := by sorry

end QAlgorithms.Papers.Independent.Independent1.P09
