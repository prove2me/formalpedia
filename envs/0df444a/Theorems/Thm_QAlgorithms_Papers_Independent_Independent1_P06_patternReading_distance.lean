-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P06_patternReading_distance
-- name    : QAlgorithms.Papers.Independent.Independent1.P06.patternReading_distance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:43:49.694563+00:00
-- url     : https://prove2.me/theorems/f2a269fc-acb0-4c95-9687-f4748c479bd2
-- title:
--   Lemma 3.8: general Z-pattern distance
-- statement:
--   Let $H_X,H_Z$ define a binary CSS memory with both distances at least $d\in\mathbb N$. Let $P\in\mathbb F_2^{r\times c}$ have full row rank and every row of Hamming weight greater than one. The prescribed Z-pattern deformation of $c$ identical memories, with $r m_X$ new data qubits indexed by pattern rows and memory X checks, satisfies
--
--   $$d_X(D_X,D_Z)\ge d,\qquad d_Z(D_X,D_Z)\ge d.$$
--
--   The conclusion includes CSS commutation and every nontrivial logical class. Sparsity belongs to the separate resource claim.
-- source:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery, arXiv:2510.14895v1, Lemma 3.8, PDF p. 21. https://arxiv.org/abs/2510.14895v1 . PDF SHA-256: 5432b21da79d052ade1546bd9aa83b711bc517ad598c27fc785a711aeaafe54e.

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

















/-- Lemma 3.8, PDF pp.20–21: a full-row-rank Z pattern with every row of weight greater
than one preserves both code distances. Sparsity belongs to the separate resource claim. -/
theorem patternReading_distance {c r n mx mz d : ℕ}
    (HX : Matrix (Fin mx) (Fin n) F2) (HZ : Matrix (Fin mz) (Fin n) F2)
    (P : Matrix (Fin r) (Fin c) F2)
    (fullRowRank : Function.Injective P.transpose.mulVec)
    (rowWeight : ∀ i, 1 < hammingNorm (P i))
    (distance : HasCSSDistance HX HZ d) :
    HasCSSDistance (readingX HX P) (readingZ HX HZ P) d := by sorry






























end QAlgorithms.Papers.Independent.Independent1.P06
