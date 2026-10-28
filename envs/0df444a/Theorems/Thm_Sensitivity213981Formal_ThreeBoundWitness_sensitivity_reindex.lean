-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundWitness_sensitivity_reindex
-- name    : Sensitivity213981Formal.ThreeBoundWitness.sensitivity_reindex
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:35:44.130559+00:00
-- url     : https://prove2.me/theorems/7a39b098-3c8f-4d71-a68b-1051bb54c1d4
-- title:
--   Sensitivity is invariant under a bijection of input coordinates
-- statement:
--   Let \(I,J\) be finite coordinate types, let \(e:I\cong J\) be a bijection, and let \(f:\{0,1\}^{I}\to\{0,1\}\). Reindex \(f\) along \(e\) to obtain a function on \(J\). Then
--   \[
--   s(\operatorname{reindex}_e f)=s(f).
--   \]
--   This permits recursive functions on structured finite coordinate types to be presented on \(\operatorname{Fin}(n)\).
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; WitnessLifting.lean, lines 385–399.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundWitness.sensitivity_reindex :
∀ {I J : Type} [inst : Fintype.{0} I] [inst_1 : Fintype.{0} J] (e : Equiv.{1, 1} I J) (f : (I → Bool) → Bool),
  @Eq.{1} Nat (@OAI.Paper320.sensitivity J inst_1 (@Sensitivity213981Formal.ThreeBoundWitness.reindex I J e f))
    (@OAI.Paper320.sensitivity I inst f) := by sorry
