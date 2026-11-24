-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SerreFinite_proof_2527071963fc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SerreFinite_proof_2527071963fc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:42.838262+00:00
-- url     : https://prove2.me/theorems/3115fec1-278f-4b6b-9e7e-b29e3314d20a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Serre Finite proof 2527071963fc: P2 M Ground Theory Heights  Heights Kleiman Serre Finite proof 2527071963fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Serre Finite proof 2527071963fc construction uses the P2 M Ground Theory Heights  Heights Kleiman Serre Finite proof 2527071963fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFinite.lean#L14-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFinite.lean#L14-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SerreFinite_proof_2527071963fc (hExact : CechExact.Statement.{u, max u v})
    (hTop : CechTop.Statement.{u, max u v}) (hFree : SerreFree.Statement.{u, max u v})
    (hPres : GradedPres.Statement.{u, v}) (hLift : GradedULift.Statement.{u, v})
    (hRet : CohomRetract.Statement.{u, v, max u v}) : SerreFinite.Statement.{u, v} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SerreFinite».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SerreFinite_proof_2527071963fc
