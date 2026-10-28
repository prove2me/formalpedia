-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_gstInvariance
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.gstInvariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:27:23.127673+00:00
-- url     : https://prove2.me/theorems/dbd3e9fc-41b3-4451-8f85-29c38de8cf83
-- title:
--   Exact GST and common-gauge invariance
-- statement:
--   Fix an $n$-qubit physical tomographic frame of density preparations and observable measurements, with invertible input and output matrices $M_{\rm in},M_{\rm out}$. Let $T$ be an invertible real gauge, fixed for all operations, and let $O_j$ be finite Kraus maps in chronological order. Form the exact measured matrices $\widetilde O_{j,a b}=\operatorname{Tr}(Q_aO_j(\rho_b))$ and $g=M_{\rm out}M_{\rm in}$. Then $g$ is invertible and
--   $$\widetilde O_j=M_{\rm out}M(O_j)M_{\rm in},\qquad
--   \widehat O_j=Tg^{-1}\widetilde O_jT^{-1}
--   =TM_{\rm in}^{-1}M(O_j)M_{\rm in}T^{-1}.$$
--   For every input and readout label $b,a$, including an empty operation sequence,
--   $$\operatorname{Tr}(Q_aO_t\cdots O_1(\rho_b))
--   =(gT^{-1})_{a,\bullet}\,\widehat O_t\cdots\widehat O_1\,T_{\bullet,b}.$$
--   This establishes prediction invariance using computed exact calibration data; estimated coordinates need not be physical states.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, Appendix E (E1)–(E7); §IX, PDF p. 7. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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























































/-- PDF pp.6–7,14,18, (E1)–(E7): physical GST data and common-gauge predictions. -/
theorem gstInvariance {n t : ℕ} (F : TomographicFrame n)
    (hin : IsUnit F.inputMatrix) (hout : IsUnit F.outputMatrix)
    (T : Matrix (PauliIndex n) (PauliIndex n) ℝ) (hT : IsUnit T)
    (O : Fin t → Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ]
      Matrix (Qubits n) (Qubits n) ℂ)
    (kraus : ∀ j, ∃ r : ℕ, ∃ K : Fin r → Matrix (Qubits n) (Qubits n) ℂ,
      O j = krausLinearMap K) :
    let g := F.gram
    let data := fun j => Matrix.of fun a b =>
      ((F.measurement a).observable * O j (F.preparation b)).trace.re
    let hat := fun j => T*g⁻¹*data j*T⁻¹
    IsUnit g ∧
    (∀ j, data j = F.outputMatrix*pauliTransferMatrix (O j)*F.inputMatrix ∧
      hat j = T*F.inputMatrix⁻¹*pauliTransferMatrix (O j)*F.inputMatrix*T⁻¹) ∧
    ∀ a b, ((F.measurement a).observable *
      ((List.ofFn O).foldl (fun X op => op X) (F.preparation b))).trace.re =
        (g*T⁻¹) a ⬝ᵥ (((List.ofFn hat).reverse.prod).mulVec (fun i => T i b)) := by sorry








end QAlgorithms.Papers.Independent.Independent1.P09
