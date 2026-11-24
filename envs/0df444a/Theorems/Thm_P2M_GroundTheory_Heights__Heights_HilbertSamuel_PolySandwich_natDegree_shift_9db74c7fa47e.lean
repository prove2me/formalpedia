-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_natDegree_shift_9db74c7fa47e
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_natDegree_shift_9db74c7fa47e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:25.788162+00:00
-- url     : https://prove2.me/theorems/b25e979e-a70c-4f9d-b08f-1b89d1257a9a
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich nat Degree shift 9db74c7fa47e: P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich nat Degree shift 9db74c7fa47e
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich nat Degree shift 9db74c7fa47e construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Poly Sandwich nat Degree shift 9db74c7fa47e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPolySandwich.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPolySandwich.lean#L31-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolySandwich
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPolySandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial Filter

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_natDegree_shift_9db74c7fa47e (p : ℚ[X]) (c : ℚ) : (p.comp (X + C c)).natDegree = p.natDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«PolySandwich».«natDegree_shift» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_natDegree_shift_9db74c7fa47e
