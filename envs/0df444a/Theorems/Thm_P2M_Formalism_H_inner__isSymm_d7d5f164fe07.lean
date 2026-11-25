-- Prove2me | Theorems.Thm_P2M_Formalism_H_inner__isSymm_d7d5f164fe07
-- name    : P2M_Formalism_H_inner__isSymm_d7d5f164fe07
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:20.916804+00:00
-- url     : https://prove2.me/theorems/515a54f4-60f7-4180-a954-453ce3a71dae
-- title:
--   P2 M Formalism H inner  is Symm d7d5f164fe07: P2 M Formalism H inner  is Symm d7d5f164fe07
-- statement:
--   The P2 M Formalism H inner  is Symm d7d5f164fe07 construction uses the P2 M Formalism H inner  is Symm d7d5f164fe07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/DualLattice.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/DualLattice.lean#L22-L29

import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.H
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem P2M_Formalism_H_inner__isSymm_d7d5f164fe07 : LinearMap.BilinForm.IsSymm (innerₗ V) := by sorry

alias «Formalism».«H».«innerₗ_isSymm» := P2M_Formalism_H_inner__isSymm_d7d5f164fe07
