-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P06_openBoundary_idling_homology
-- name    : QAlgorithms.Papers.Independent.Independent1.P06.openBoundary_idling_homology
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:46:03.862166+00:00
-- url     : https://prove2.me/theorems/e40373fd-1bbd-4281-9936-05ff67418f4e
-- title:
--   AppendixA.1: open-boundary idling homology
-- statement:
--   Let $C_\bullet$ be a finite binary CSS complex supported in degrees $0,1,2$, and let $\ell>0$ be the repetition length. Let $F=R\otimes C$, and let $F'_X$ be its prescribed two-endpoint cone. Let $F_{\rm dual}$ and $F'_Z$ be the cochain-oriented bulk and cone obtained by the specified degree-reversing dual constructions. Put $m_X=\dim C_0$ and $m_Z=\dim C_2$. Then
--
--   $$\begin{aligned}\dim H_1(F'_X)+\dim H_0(C)&=\dim H_1(F)+2m_X,&\dim H_0(F'_X)&=0,\\\dim H_2(F'_Z)+\dim H_2(C)&=\dim H_2(F_{\rm dual})+2m_Z,&\dim H_3(F'_Z)&=0.\end{aligned}$$
--
--   These retain all boundary homology classes, including immediately terminating classes. They imply no operational fault-distance bound by themselves.
-- source:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery, arXiv:2510.14895v1, AppendixA.1, PDF p. 65. https://arxiv.org/abs/2510.14895v1 . PDF SHA-256: 5432b21da79d052ade1546bd9aa83b711bc517ad598c27fc785a711aeaafe54e.

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









































/-- Appendix A.1, PDF p.65: both open temporal orientations and all new boundary
classes. This computes cone homology, with no operational fault-distance claim. -/
theorem openBoundary_idling_homology (C : Surgery.BasedBinaryComplex)
    (css : Surgery.IsCSSComplex C) (l : ℕ) (positive : 0 < l) :
    let F := Surgery.tensorComplex (Surgery.repetitionComplex l positive) C
    let FX := Surgery.openIdlingVolume C css l positive .X
    let FZ := Surgery.openIdlingVolume C css l positive .Z
    let Fdual := Surgery.dualComplex 3
      (Surgery.tensorComplex (Surgery.repetitionComplex l positive) (Surgery.dualComplex 2 C))
    (Module.finrank F2 (Surgery.Homology FX 1) + Module.finrank F2 (Surgery.Homology C 0) =
      Module.finrank F2 (Surgery.Homology F 1) + 2 * Fintype.card (Surgery.Basis C 0)) ∧
    Module.finrank F2 (Surgery.Homology FX 0) = 0 ∧
    (Module.finrank F2 (Surgery.Homology FZ 2) + Module.finrank F2 (Surgery.Homology C 2) =
      Module.finrank F2 (Surgery.Homology Fdual 2) + 2 * Fintype.card (Surgery.Basis C 2)) ∧
    Module.finrank F2 (Surgery.Homology FZ 3) = 0 := by sorry






end QAlgorithms.Papers.Independent.Independent1.P06
