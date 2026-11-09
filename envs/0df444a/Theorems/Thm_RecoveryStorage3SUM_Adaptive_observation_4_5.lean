-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_observation_4_5
-- name    : RecoveryStorage3SUM.Adaptive.observation_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:31.946599+00:00
-- url     : https://prove2.me/theorems/840a351d-2564-4958-948f-ed03e764a677
-- title:
--   Observation 4.5 — verified recovery only produces pairs of $M_r$
-- statement:
--   Fix a run with prime $p$, a residue $r\in[p]$, and arbitrary inverter answers. Then every element of $\widehat A$ is a first coordinate of some pair of $M_r$, and the output of Recover$(r)$ is a subset of $M_r$.
--
--   So a failing inverter can only lose pairs, never invent them. This is why the count $z$ can only overestimate.
--
--   Differences from the source:
--   - generalization: the source run, its cap L and its FN answers → arbitrary finite integer sets A, B and R, arbitrary inverter answers and partitions, any cap, any K and L, and any modulus p with r<p, without size, sampling, coverage, load or polynomial-bound assumptions; reason: verification and the residue bucket rule alone imply both conclusions; every source run and cap is included
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Observation 4.5, p.12

import Mathlib
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Construction

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

/-- Observation 4.5, p.12: whatever the inverters answer, every element of `Â` is a first coordinate
of a pair of `M_r`, and the output of `Recover(r)` is a subset of `M_r`. -/
theorem observation_4_5 {A : Finset ℤ} {K L : ℕ} (B R : Finset ℤ) (run : Attempt A K L)
    (inv : Fin K → Fin L → ℕ → Option ℕ) (cap r : ℕ) (hr : r < run.p) :
    (∀ a ∈ discovered B R run inv r, ∃ b, (a, b) ∈ unmarkedClass A B R run.p r) ∧
      recoverOutput B R run inv cap r ⊆ unmarkedClass A B R run.p r := by sorry

end RecoveryStorage3SUM.Adaptive
