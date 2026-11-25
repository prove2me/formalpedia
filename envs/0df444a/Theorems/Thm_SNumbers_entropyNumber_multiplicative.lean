-- Prove2me | Theorems.Thm_SNumbers_entropyNumber_multiplicative
-- name    : SNumbers.entropyNumber_multiplicative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:44.308516+00:00
-- url     : https://prove2.me/theorems/51e8ec1b-f9fe-5fc2-9c33-bc728b5cdb5e
-- title:
--   SNumbers: entropy Number multiplicative
-- statement:
--   **Multiplicativity of the entropy numbers**:
--   `e_{n+m}(B ∘ S) ≤ e_n B · e_m S`. Again the budgets of balls multiply, so the
--   indices add.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L450-L475
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L450-L475

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.entropyNumber_multiplicative (B : Y →L[𝕜] Z) (S : X →L[𝕜] Y) (n m : ℕ) :
    entropyNumber (B.comp S) (n + m) ≤ entropyNumber B n * entropyNumber S m := by sorry
