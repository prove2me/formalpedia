-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_noiseFactorization
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.noiseFactorization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:32:32.83876+00:00
-- url     : https://prove2.me/theorems/bab80635-762a-4545-97c6-c0301e571295
-- title:
--   Channel factorization around an ideal gate
-- statement:
--   Let $U$ be an ideal $n$-qubit unitary and let $G$ be any channel in finite normalized Kraus form. Set $N_b=\operatorname{id}$ and $N_a=G\circ[U^\dagger]$, where $[U](X)=UXU^\dagger$. Then
--   $$N_a,N_b\text{ are channels},\qquad G=N_a\circ[U]\circ N_b.$$
--   This constructs the before/after noise model explicitly. The required inverse is the ideal unitary channel; invertibility of the noisy channel is unnecessary.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, Appendix H, PDF p. 16. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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




























































/-- PDF p.16, Appendix H: explicit before/after channel factorization around ideal unitary. -/
theorem noiseFactorization {n : ℕ} (U : Matrix.unitaryGroup (Qubits n) ℂ)
    (G : Superop (Qubits n) (Qubits n)) (hG : IsChannel G) :
    let before : Superop (Qubits n) (Qubits n) := id
    let after := G ∘ conjSuperop (star (U : Matrix (Qubits n) (Qubits n) ℂ))
    IsChannel before ∧ IsChannel after ∧
    G = after ∘ conjSuperop (U : Matrix (Qubits n) (Qubits n) ℂ) ∘ before := by sorry



end QAlgorithms.Papers.Independent.Independent1.P09
