-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_gateFidelity_operatorBasis
-- name    : QAlgorithms.Papers.Independent.Independent1.P10.gateFidelity_operatorBasis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:25:44.368128+00:00
-- url     : https://prove2.me/theorems/42947d0a-770d-4afb-9d7c-d53c9b0757f5
-- title:
--   General qudit average gate fidelity formula
-- statement:
--   Let $d>0$, let $\mathcal E$ be a completely positive trace-preserving map, and let $U$ be a unitary target. Let $(U_j)_{j=1}^{d^2}$ be a complex operator basis of unitaries satisfying $\operatorname{tr}(U_j^\dagger U_k)=d\delta_{jk}$. The normalized Haar average gate overlap is
--
--   $$\overline F(\mathcal E,U)=\frac{\sum_{j=1}^{d^2}\operatorname{Re}\operatorname{tr}(U U_j^\dagger U^\dagger\mathcal E(U_j))+d^2}{d^2(d+1)}.$$
--
--   The target inverse conjugates the channel output. This is the paper's general qudit formula, with no unitality assumption.
-- source:
--   A simple formula for the average gate fidelity of a quantum dynamical operation, arXiv:quant-ph/0205035v2, Eq. (17): the paper's general qudit average gate fidelity formula, PDF p. 2. https://arxiv.org/abs/quant-ph/0205035v2 . PDF SHA-256: a59643207560eeaa2b638e69af6528c299e929c2eab2af32f0117a5d6a2f2f2a.

import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P10_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P10















/-- Nielsen, PDF p.2, Eq. (17): general qudit gate-fidelity formula. U is the
separate target gate; the basis need not contain the identity. -/
theorem gateFidelity_operatorBasis (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (B : OrthogonalUnitaryOperatorBasis d) :
    gateFidelity d hd E U =
      ((∑ j, ((U : Matrix (Fin d) (Fin d) ℂ)*star (B.basis j)*
        star (U : Matrix (Fin d) (Fin d) ℂ)*E (B.basis j)).trace.re)+(d : ℝ)^2) /
          ((d : ℝ)^2*((d : ℝ)+1)) := by sorry



end QAlgorithms.Papers.Independent.Independent1.P10
