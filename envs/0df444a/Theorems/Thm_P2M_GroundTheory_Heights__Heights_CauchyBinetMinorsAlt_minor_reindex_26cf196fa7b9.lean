-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_minor_reindex_26cf196fa7b9
-- name    : P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_minor_reindex_26cf196fa7b9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:17:52.346269+00:00
-- url     : https://prove2.me/theorems/cb17e19e-b6ad-4025-927f-ffdfd424a71c
-- title:
--   P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt minor reindex 26cf196fa7b9: P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt minor reindex 26cf196fa7b9
-- statement:
--   The P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt minor reindex 26cf196fa7b9 construction uses the P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt minor reindex 26cf196fa7b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCauchyBinetMinors.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCauchyBinetMinors.lean#L22-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCauchyBinetMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Finset
open GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt

theorem P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_minor_reindex_26cf196fa7b9 {R : Type*} [CommRing R] {n k : ℕ} (X : Matrix (Fin n) (Fin n) R)
    (s : Finset (Fin n)) (hk : s.card = k) :
    (X.submatrix ((↑) : s → Fin n) ((↑) : s → Fin n)).det =
      (X.submatrix (s.orderEmbOfFin hk) (s.orderEmbOfFin hk)).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CauchyBinetMinorsAlt».«minor_reindex» := P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_minor_reindex_26cf196fa7b9
