-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_gateFidelity_eq_one_iff
-- name    : QAlgorithms.Papers.Independent.Independent1.P10.gateFidelity_eq_one_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:26:19.260394+00:00
-- url     : https://prove2.me/theorems/3ce12cba-771e-4ad7-b29d-ebd3c5785f8b
-- title:
--   Unit average gate fidelity characterizes perfect implementation
-- statement:
--   Let $d>0$, let $\mathcal E$ be a completely positive trace-preserving map on $d$-dimensional matrices, and let $U$ be a unitary target. Let $\overline F(\mathcal E,U)$ denote the normalized Haar average of $\langle\psi|U^\dagger\mathcal E(|\psi\rangle\langle\psi|)U|\psi\rangle$. Then
--
--   $$\overline F(\mathcal E,U)=1\quad\Longleftrightarrow\quad\mathcal E(X)=UXU^\dagger\text{ for every matrix }X.$$
--
--   Thus unit overlap fidelity characterizes exact implementation of the target channel, including its action on all density inputs.
-- source:
--   A simple formula for the average gate fidelity of a quantum dynamical operation, arXiv:quant-ph/0205035v2, Unnumbered claim following Eq. (2): unit average gate fidelity iff perfect implementation, PDF p. 1. https://arxiv.org/abs/quant-ph/0205035v2 . PDF SHA-256: a59643207560eeaa2b638e69af6528c299e929c2eab2af32f0117a5d6a2f2f2a.

import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P10_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P10











/-- Nielsen, PDF p.1, claim after Eq. (2): unit average gate fidelity is
perfect implementation, as equality of channels on every operator. -/
theorem gateFidelity_eq_one_iff (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    gateFidelity d hd E U = 1 ↔ E = conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) := by sorry







end QAlgorithms.Papers.Independent.Independent1.P10
