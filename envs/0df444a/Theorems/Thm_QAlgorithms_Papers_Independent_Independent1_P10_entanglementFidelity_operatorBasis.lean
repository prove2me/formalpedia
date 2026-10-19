-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_entanglementFidelity_operatorBasis
-- name    : QAlgorithms.Papers.Independent.Independent1.P10.entanglementFidelity_operatorBasis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:25:16.936649+00:00
-- url     : https://prove2.me/theorems/29c528d6-c846-4a4d-84f4-ab0d7c7328a2
-- title:
--   Entanglement fidelity in an orthogonal unitary operator basis
-- statement:
--   Let $d>0$ and let $\mathcal E$ be a completely positive trace-preserving map. Let $(U_j)_{j=1}^{d^2}$ be a complex operator basis consisting of unitaries with $\operatorname{tr}(U_j^\dagger U_k)=d\delta_{jk}$. With $F_e$ the overlap of the normalized maximally entangled state before and after applying $\mathcal E$ to its system register,
--
--   $$F_e(\mathcal E)=\frac{1}{d^3}\sum_{j=1}^{d^2}\operatorname{Re}\operatorname{tr}(U_j^\dagger\mathcal E(U_j)).$$
--
--   This expresses entanglement fidelity using the channel action on an operator basis.
-- source:
--   A simple formula for the average gate fidelity of a quantum dynamical operation, arXiv:quant-ph/0205035v2, Eq. (16): entanglement fidelity in an orthogonal unitary operator basis, PDF p. 2. https://arxiv.org/abs/quant-ph/0205035v2 . PDF SHA-256: a59643207560eeaa2b638e69af6528c299e929c2eab2af32f0117a5d6a2f2f2a.

import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P10_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P10














/-- Nielsen, PDF p.2, Eq. (16): entanglement fidelity in any orthogonal unitary
operator basis. Real parts transcribe the real-valued fidelity. -/
theorem entanglementFidelity_operatorBasis (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (B : OrthogonalUnitaryOperatorBasis d) :
    QuditFidelity.entanglementFidelity d hd E =
      (∑ j, (star (B.basis j)*E (B.basis j)).trace.re)/(d : ℝ)^3 := by sorry




end QAlgorithms.Papers.Independent.Independent1.P10
