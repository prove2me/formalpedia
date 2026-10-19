-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_pauliTransferIdentities
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.pauliTransferIdentities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:24:42.395637+00:00
-- url     : https://prove2.me/theorems/647e37fb-ec32-490e-8841-4db3d5ca04c4
-- title:
--   Pauli transfer identities
-- statement:
--   Let $\rho$ be an $n$-qubit density matrix and $Q$ a Hermitian observable. Let $\mathcal O_1,\ldots,\mathcal O_t$ be finite Kraus maps, with no trace-preservation requirement, applied in chronological order. Write $\rho_f=\mathcal O_t\cdots\mathcal O_1(\rho)$, $r(\rho)_\sigma=\operatorname{Tr}(\sigma\rho)$, $q(Q)_\sigma=2^{-n}\operatorname{Tr}(\sigma Q)$ and $M(\mathcal O)_{\sigma,\tau}=2^{-n}\operatorname{Tr}(\sigma\mathcal O(\tau))$, in the order $I,X,Y,Z$ on each wire. Then
--   $$r(\rho_f)=M(\mathcal O_t)\cdots M(\mathcal O_1)r(\rho),\qquad
--   \operatorname{Tr}(Q\rho_f)=q(Q)\cdot M(\mathcal O_t)\cdots M(\mathcal O_1)r(\rho).$$
--   Traces in these coordinates are real. The empty circuit has identity transfer matrix. These identities connect the physical experiments to real linear algebra.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, §III; Appendix A (A1)–(A5), PDF p. 13. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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










































/-- PDF pp.3,12–13, Appendix A (A1)–(A5): Pauli coordinates and chronological composition. -/
theorem pauliTransferIdentities {n t : ℕ}
    (rho Q : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsDensityMatrix rho)
    (hQ : Q.IsHermitian) (r : Fin t → ℕ)
    (K : (j : Fin t) → Fin (r j) → Matrix (Qubits n) (Qubits n) ℂ) :
    let maps := fun j => krausLinearMap (K j)
    let final := (List.ofFn maps).foldl (fun X O => O X) rho
    pauliStateVector final =
      ((List.ofFn fun j => pauliTransferMatrix (maps j)).reverse.prod).mulVec
        (pauliStateVector rho) ∧
    (Q * final).trace.re = pauliObservableRow Q ⬝ᵥ
      (((List.ofFn fun j => pauliTransferMatrix (maps j)).reverse.prod).mulVec
        (pauliStateVector rho)) := by sorry





















end QAlgorithms.Papers.Independent.Independent1.P09
