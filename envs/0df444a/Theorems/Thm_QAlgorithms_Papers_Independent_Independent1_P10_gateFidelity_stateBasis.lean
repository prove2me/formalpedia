-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_gateFidelity_stateBasis
-- name    : QAlgorithms.Papers.Independent.Independent1.P10.gateFidelity_stateBasis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:25:58.838499+00:00
-- url     : https://prove2.me/theorems/66f271a2-5c6a-4b22-b289-cb0c715697dd
-- title:
--   Average gate fidelity from a density operator basis
-- statement:
--   Let $d>0$, let $\mathcal E$ be a completely positive trace-preserving map, and let $U$ be a unitary target. Let $(U_j)_{j=1}^{d^2}$ be a complex operator basis of unitaries with $\operatorname{tr}(U_j^\dagger U_k)=d\delta_{jk}$. Let $(\rho_k)_{k=1}^{d^2}$ be a complex operator basis whose elements are density matrices. Define the unique complex coordinates $\alpha_{jk}$ by $U_j=\sum_k\alpha_{jk}\rho_k$. Then
--
--   $$\overline F(\mathcal E,U)=\frac{\sum_{j,k}\operatorname{Re}\!\left[\alpha_{jk}\operatorname{tr}(U U_j^\dagger U^\dagger\mathcal E(\rho_k))\right]+d^2}{d^2(d+1)}.$$
--
--   This gives an exact algebraic determination from the outputs on the state basis. It asserts no finite-shot accuracy or sample-cost guarantee.
-- source:
--   A simple formula for the average gate fidelity of a quantum dynamical operation, arXiv:quant-ph/0205035v2, Eq. (19): average gate fidelity from a preparable state operator basis, PDF p. 3. https://arxiv.org/abs/quant-ph/0205035v2 . PDF SHA-256: a59643207560eeaa2b638e69af6528c299e929c2eab2af32f0117a5d6a2f2f2a.

import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P10_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P10

















/-- Nielsen, PDF pp.2--3, Eq. (19): the preparable-state operator-basis formula.
Complex coefficients are computed by repr; take the real part after multiplying.
The printed real-superposition example on p.2 is not used as a basis witness. -/
theorem gateFidelity_stateBasis (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (B : OrthogonalUnitaryOperatorBasis d)
    (R : StateOperatorBasis d) :
    gateFidelity d hd E U =
      ((∑ j, ∑ k, ((R.basis.repr (B.basis j) k)*
        ((U : Matrix (Fin d) (Fin d) ℂ)*star (B.basis j)*
          star (U : Matrix (Fin d) (Fin d) ℂ)*E (R.basis k)).trace).re)+(d : ℝ)^2) /
            ((d : ℝ)^2*((d : ℝ)+1)) := by sorry

end QAlgorithms.Papers.Independent.Independent1.P10
