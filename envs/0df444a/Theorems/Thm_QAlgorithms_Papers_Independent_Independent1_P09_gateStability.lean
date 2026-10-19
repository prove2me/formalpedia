-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_gateStability
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.gateStability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:27:49.507166+00:00
-- url     : https://prove2.me/theorems/fd75adaa-034d-4070-84ed-080607b36e90
-- title:
--   Symbolic gate stability with positive denominator
-- statement:
--   Let $M_j$ be local real input-frame matrices, $M_0$ the computed reference input matrix, $M=\bigotimes_jM_j$, $T=M_0^{\otimes n}$, and $e=\max_j\|M_j-M_0\|_2$. Let $O,O_0$ be real operation matrices and put $e_O=\|O-O_0\|_2$, $s=s_{\min}(M_0)$ and $e_n=(\|M_0\|_2+e)^n-\|M_0\|_2^n$. Assume $e_n<s^n$. Then $M$ is invertible and
--   $$\|M-T\|_2\le e_n,\qquad \|M^{-1}\|_2\le(s^n-e_n)^{-1}.$$
--   For the computed GST estimate $\widehat O=TM^{-1}OMT^{-1}$,
--   $$\|\widehat O-O_0\|_2\le
--   \frac{2e_n}{s^n-e_n}(\|O_0\|_2+e_O)+e_O.$$
--   The empty tensor case has $e_n=0$ and identity gauge. This states the source proof's small-error domain, not a bound with a nonpositive denominator.
--
--   **Correction to the printed source.**
--
--   Printed: F14 and its use in F7 display an inverse norm bound without an explicit small-error inequality at that point.
--
--   Corrected: Require e_n<s_min(Min0)^n before applying the displayed reciprocal bound; keep all symbolic norms and the printed F7 formula.
--
--   Reason: The proof invokes F10 and C3, whose strict smallness condition makes the denominator positive. Invertibility alone is insufficient; this proof-domain clarification requires independent moderation.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, Appendix F (F7),(F8),(F13),(F14), PDF p. 15. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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

























































/-- PDF p.15, (F7),(F8),(F13),(F14): proof-domain reading with positive denominator. -/
theorem gateStability {n : ℕ} (Min : Fin n → Matrix (Fin 4) (Fin 4) ℝ)
    (O Oideal : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ)
    (small : (specNorm referenceInput + maxLocalError Min referenceInput)^n -
      specNorm referenceInput^n < (leastSingular (by omega) referenceInput)^n) :
    let ein := (specNorm referenceInput + maxLocalError Min referenceInput)^n -
      specNorm referenceInput^n
    let base := tensorMatrix (fun _ : Fin n => referenceInput)
    let physical := tensorMatrix Min
    let hat := base*physical⁻¹*O*physical*base⁻¹
    IsUnit physical ∧ specNorm (physical-base) ≤ ein ∧
    specNorm physical⁻¹ ≤ ((leastSingular (by omega) referenceInput)^n-ein)⁻¹ ∧
    specNorm (hat-Oideal) ≤
      2*ein/((leastSingular (by omega) referenceInput)^n-ein)*
        (specNorm Oideal+specNorm (O-Oideal)) + specNorm (O-Oideal) := by sorry






end QAlgorithms.Papers.Independent.Independent1.P09
