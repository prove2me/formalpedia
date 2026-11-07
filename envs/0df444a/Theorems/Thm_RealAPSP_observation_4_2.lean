-- Prove2me | Theorems.Thm_RealAPSP_observation_4_2
-- name    : RealAPSP.observation_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:09.904193+00:00
-- url     : https://prove2.me/theorems/60a9a555-4711-47db-997f-297c1dc7ec6e
-- title:
--   Observation 4.2
-- statement:
--   If $A\in(\mathbb R\cup\{\bot\})^{n\times n}$ has $\Delta$-approximate rank at most $r$, then for every positive integer $c$ it has $\Delta/c$-approximate rank at most $(2c+1)r$. Given a decomposition, the new decomposition can be computed in time $O(n^2c)$.
--
--   This makes approximate rank insensitive to the scale up to constants, which the proof of Theorem 1.1 needs to change between $2\Delta$ and $\Delta/2$.
--
--   **Formalization Note** The output real cells hold $2c\cdot U'$ and $2c\cdot V'$, since $\Delta/(2c)$ is not an integer combination of the inputs.
--
--   Differences from the source:
--   - reading: the comparison-addition model of §1.2, p.3, which also names a "realistic" variant → the machine RealAPSP.Machine: the published GuardedSSSP core plus rneg, unit cost, stuck on word overflow, fair coins preloaded in memory; reason: the realistic variant defers to [FPS26, Section 1.1], which is not held, and Theorem 1.1 does not name it; rneg is simulable at constant overhead by pairs p − q
--   - encoding: input and output as mathematical objects → fixed cell layouts for the parameters, matrices and outputs, given in the docstrings; reason: a machine statement needs a layout; every layout used is within a constant factor of any other
--   - encoding: "assume that we also have access to a ∆-approximate rank-r decomposition" (p.11) → the decomposition (U, V, S) is part of the input; reason: as the page says
--   - encoding: the real outputs U′, V′ → 2c•U′ and 2c•V′ in real output cells; reason: the machine computes only integer combinations of its input reals
--   - encoding: "We can compute it" with no randomness in the proof → a deterministic run; reason: the printed construction is deterministic
--   - encoding: matrices of size n, n unrestricted → 1 ≤ n; reason: at n = 0 there are no entries and no triangles, so the instance is empty and the claim has no content
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Observation 4.2, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_RealAPSP_Rank

namespace RealAPSP

/-- **Observation 4.2.** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.11 (PDF p.13).

Two clauses: the rank bound itself, for every `c ∈ ℤ_{>0}`; and a deterministic program computing the new decomposition in time `O(n²c)`, writing `2c•U'` and `2c•V'` since the machine has no division. -/
theorem observation_4_2 :
    (∀ (n r c : ℕ), 1 ≤ c → ∀ Δ : ℝ, 0 ≤ Δ → ∀ (A : Mat ℝ n) (U : Fin n → Fin r → ℝ) (V : Fin r → Fin n → ℝ)
        (S : Fin n → Fin n → Option (Fin r)), IsRankDecomp Δ A r U V S →
      ∃ (U' : Fin n → Fin ((2 * c + 1) * r) → ℝ) (V' : Fin ((2 * c + 1) * r) → Fin n → ℝ)
        (S' : Fin n → Fin n → Option (Fin ((2 * c + 1) * r))), IsRankDecomp (Δ / c) A ((2 * c + 1) * r) U' V' S') ∧
    ∃ (P : Program) (κ : ℝ), ∀ (n r c : ℕ), 1 ≤ n → 1 ≤ c → ∀ Δ : ℝ, 0 ≤ Δ →
      ∀ (A : Mat ℝ n) (U : Fin n → Fin r → ℝ) (V : Fin r → Fin n → ℝ) (S : Fin n → Fin n → Option (Fin r)),
        IsRankDecomp Δ A r U V S →
        Runs P (n + r + c + 2) ([(n : ℤ), (r : ℤ), (c : ℤ)] ++ flagCells A ++ decompInts S)
          ([Δ] ++ valueCells A ++ decompReals U V) (κ * (n : ℝ) ^ 2 * (c : ℝ))
          (HasRankOutput (Δ / c) A ((2 * c + 1) * r) (2 * c)) := by sorry

end RealAPSP
