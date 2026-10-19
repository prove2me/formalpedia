-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_perturbationInvertibility
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.perturbationInvertibility
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:28:44.340499+00:00
-- url     : https://prove2.me/theorems/b2a881be-77bc-4100-b39b-0cf2adb89d83
-- title:
--   Perturbation invertibility and inverse norm
-- statement:
--   Let $d\ge1$ and let $A_0,A$ be real $d\times d$ matrices. Define $s=\sqrt{\lambda_{\min}(A_0^{\mathsf T}A_0)}$, with eigenvalues counted with multiplicity. All norms below are Euclidean vector norms or their induced operator norms. If $e=\|A-A_0\|_2<s$, then
--   $$A\text{ is invertible},\qquad
--   \|Ax\|_2\ge(s-e)\|x\|_2\quad\text{for every }x,\qquad
--   \|A^{-1}\|_2\le(s-e)^{-1}.$$
--   The strict inequality makes the denominator positive and the lower bound strictly positive for nonzero $x$. This is the symbolic robustness argument used for operation and SPAM completeness.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, Appendix C (C1)–(C3); Appendix F (F10), PDF p. 13. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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

















































/-- PDF pp.13,15, (C1)–(C3),(F10): perturbation invertibility and inverse operator norm. -/
theorem perturbationInvertibility {d : ℕ} (hd : 0 < d)
    (A0 A : Matrix (Fin d) (Fin d) ℝ)
    (small : specNorm (A-A0) < leastSingular hd A0) :
    IsUnit A ∧
    (∀ x : EuclideanSpace ℝ (Fin d),
      (leastSingular hd A0-specNorm (A-A0))*‖x‖ ≤
        ‖WithLp.toLp 2 (A.mulVec (WithLp.ofLp x))‖) ∧
    specNorm A⁻¹ ≤ (leastSingular hd A0-specNorm (A-A0))⁻¹ := by sorry














end QAlgorithms.Papers.Independent.Independent1.P09
