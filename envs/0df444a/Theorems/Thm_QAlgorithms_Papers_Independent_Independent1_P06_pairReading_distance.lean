-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P06_pairReading_distance
-- name    : QAlgorithms.Papers.Independent.Independent1.P06.pairReading_distance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:43:59.267489+00:00
-- url     : https://prove2.me/theorems/b7834d18-1e79-44e7-ab26-51a90aef77fc
-- title:
--   Lemma 3.4: pair-reading distance
-- statement:
--   Let $H_X,H_Z$ define a binary CSS memory with X and Z distances at least $d\in\mathbb N$. Its prescribed pair-reading deformation has check matrices $D_X,D_Z$ satisfying
--
--   $$d_X(D_X,D_Z)\ge d,\qquad d_Z(D_X,D_Z)\ge d.$$
--
--   A lower distance bound quantifies over every nontrivial normalizer class modulo stabilizers; the distance is infinite when no such class exists. This is a spatial code-distance assertion.
-- source:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery, arXiv:2510.14895v1, Lemma 3.4, PDF p. 19. https://arxiv.org/abs/2510.14895v1 . PDF SHA-256: 5432b21da79d052ade1546bd9aa83b711bc517ad598c27fc785a711aeaafe54e.

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
















/-- Lemma 3.4, PDF p.19: both distances of the actual pair-reading check matrices are
at least d. No cleaning lemma is assumed. -/
theorem pairReading_distance {n mx mz d : ℕ}
    (HX : Matrix (Fin mx) (Fin n) F2) (HZ : Matrix (Fin mz) (Fin n) F2)
    (distance : HasCSSDistance HX HZ d) :
    HasCSSDistance (readingX HX pairPattern) (readingZ HX HZ pairPattern) d := by sorry































end QAlgorithms.Papers.Independent.Independent1.P06
