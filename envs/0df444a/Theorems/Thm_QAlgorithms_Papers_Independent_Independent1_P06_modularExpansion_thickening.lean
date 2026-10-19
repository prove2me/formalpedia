-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P06_modularExpansion_thickening
-- name    : QAlgorithms.Papers.Independent.Independent1.P06.modularExpansion_thickening
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:43:55.276986+00:00
-- url     : https://prove2.me/theorems/567a5303-f789-4a0a-a3a0-a050f8a4007d
-- title:
--   Theorem 7.8: thickening boosts modular expansion
-- statement:
--   Let $G\in\mathbb F_2^{V\times E}$ be a finite incidence matrix, $W\le\mathbb F_2^V$, and $U$ its support union. Put $D_W(v)=\min_{w\in W}\lvert(v|_U)+w\rvert$, where restriction to $U$ is zero extended and bars denote Hamming weight. For $t,M>0$, suppose $|G^Tv|\ge M\min(t,D_W(v))$ for every binary vector $v$. Let the integer $L\ge1$ satisfy $L\ge1/M$, and form $G_L=[G\otimes I_L,I_V\otimes R_L]$, with $R_L$ the path incidence on $L$ vertices. At any selected level $\ell<L$, embed $W$ as $W_\ell$. Then
--
--   $$|G_L^Tv|\ge\min(t,D_{W_\ell}(v))\quad\text{for every }v.$$
--
--   Thus the thickening has certified modular expansion at least one at every choice of a single level. Cut certificates avoid asserting a largest finite expansion on degenerate inputs.
-- source:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery, arXiv:2510.14895v1, Theorem 7.8, PDF p. 37. https://arxiv.org/abs/2510.14895v1 . PDF SHA-256: 5432b21da79d052ade1546bd9aa83b711bc517ad598c27fc785a711aeaafe54e.

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


































/-- Theorem 7.8, PDF p.37 and pp.87–88: positive certified expansion M and an integer
L at least 1/M give certified expansion one at every selected level. -/
theorem modularExpansion_thickening {V E : Type*} [Fintype V] [Fintype E]
    (G : Matrix V E F2) (W : Submodule F2 (V → F2)) (t M : ℝ)
    (expansion : HasModularExpansion G W t M) (positive : 0 < M)
    (L : ℕ) (levels : 1 ≤ L) (enough : M⁻¹ ≤ (L : ℝ)) :
    ∀ ell : Fin L, HasModularExpansion (thickIncidence G L) (levelSpace W L ell) t 1 := by sorry













end QAlgorithms.Papers.Independent.Independent1.P06
