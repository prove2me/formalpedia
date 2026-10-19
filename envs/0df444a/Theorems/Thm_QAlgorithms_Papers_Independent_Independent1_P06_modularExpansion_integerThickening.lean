-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P06_modularExpansion_integerThickening
-- name    : QAlgorithms.Papers.Independent.Independent1.P06.modularExpansion_integerThickening
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:43:57.792178+00:00
-- url     : https://prove2.me/theorems/20d6f64b-b6c1-4f3f-bc01-e30c06c9bee1
-- title:
--   Corollary 7.10: t-fold thickening suffices
-- statement:
--   Let $G\in\mathbb F_2^{V\times E}$ be finite and $\ker G^T\subseteq W\le\mathbb F_2^V$. For an integer $t\ge1$, form $G_t=[G\otimes I_t,I_V\otimes R_t]$. Embed $W$ at any one level $\ell<t$ as $W_\ell$, and write $U_\ell$ for its support union. Then
--
--   $$|G_t^Tv|\ge\min\{t,\min_{w\in W_\ell}\lvert(v|_{U_\ell})+w\rvert\}\quad\text{for every }v.$$
--
--   Restrictions are zero extended and weights are Hamming weights. Integer $t$-fold thickening thus certifies modular expansion one.
-- source:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery, arXiv:2510.14895v1, Corollary 7.10, PDF p. 37. https://arxiv.org/abs/2510.14895v1 . PDF SHA-256: 5432b21da79d052ade1546bd9aa83b711bc517ad598c27fc785a711aeaafe54e.

import Definitions.Def_QAlgorithms_Defs_SurgeryFaultComplexes
import Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
set_option autoImplicit false

/-!
# Fast and fault-tolerant logical measurements (arXiv:2510.14895v1)

Paper-local definitions and statement-only targets. Deferred nodes are recorded in the
assigned unit's HARD.md and GAPS.json. No operational fault-distance lower bound is
inferred from the open-boundary homology calculation.
-/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P06




































/-- Corollary 7.10, PDF pp.37–38: positive integer t-fold thickening at any one level. -/
theorem modularExpansion_integerThickening {V E : Type*} [Fintype V] [Fintype E]
    (G : Matrix V E F2) (W : Submodule F2 (V → F2))
    (kernel : LinearMap.ker G.transpose.mulVecLin ≤ W) (t : ℕ) (positive : 1 ≤ t) :
    ∀ ell : Fin t, HasModularExpansion (thickIncidence G t) (levelSpace W t ell) (t : ℝ) 1 := by sorry











end QAlgorithms.Papers.Independent.Independent1.P06
