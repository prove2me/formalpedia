-- Prove2me | Theorems.Thm_RealAPSP_observation_5_3
-- name    : RealAPSP.observation_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:17.970128+00:00
-- url     : https://prove2.me/theorems/1f296d02-e5a8-43af-9a57-91556702c24f
-- title:
--   Observation 5.3 (Number of Approximate Solutions)
-- statement:
--   Let $c_1>0$ be the constant of Lemma 5.1 (ii). There are $C_0,c>0$ such that if $L\ge C_0K$, then for any marking of the edges with at least $c_1n^3/K$ $2\Delta$-approximate solutions and at most $6n^3/L$ of them involving an unpopular edge:
--
--   1. the number of $2\Delta$-approximate solutions of type 1 (only popular edges) is at least $cn^3/K$;
--   2. the number of $2\Delta$-approximate solutions of types 2 and 3 (some unpopular edge) is at most $6n^3/L$.
--
--   This shows that at each iteration many solutions have only popular edges, which bounds the number of iterations.
--
--   Differences from the source:
--   - generalization: the output of Lemmas 5.1 and 5.2 → any marking and scale with the two counts; reason: those are the only facts used; the lemmas supply them
--   - encoding: O(n³/L) → the explicit constant 6; reason: Lemma 5.2 (ii)
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Observation 5.3, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_RealAPSP_Triangles

namespace RealAPSP

/-- **Observation 5.3 (Number of Approximate Solutions).** Fischer, Polak, Schmidt, *Real-to-Integer Reduction for All-Pairs Shortest Paths*, arXiv:2611.04847 (held file sha256 a3dc0096…), p.17 (PDF p.19).

Take the lower bound `c₁n³/K` on the number of `2∆`-approximate solutions from Lemma 5.1 (ii) and the upper bound `6n³/L` on those with an unpopular edge from Lemma 5.2 (ii). If `L ≥ C₀K`, then there are at least `c·n³/K`
solutions of type 1 and at most `6n³/L` of types 2 and 3. -/
theorem observation_5_3 :
    ∀ c₁ : ℝ, 0 < c₁ → ∃ C₀ c : ℝ, 0 < C₀ ∧ 0 < c ∧ ∀ (n : ℕ) (K L : ℝ), 1 ≤ K → 1 ≤ L → C₀ * K ≤ L →
      ∀ (Δ : ℝ) (pop : Marking n) (A B C : Mat ℝ n),
        c₁ * (n : ℝ) ^ 3 / K ≤ approxCount (2 * Δ) A B C →
        (unpopularCount (2 * Δ) pop A B C : ℝ) ≤ 6 * (n : ℝ) ^ 3 / L →
        c * (n : ℝ) ^ 3 / K ≤ popularCount (2 * Δ) pop A B C ∧
        (unpopularCount (2 * Δ) pop A B C : ℝ) ≤ 6 * (n : ℝ) ^ 3 / L := by sorry

end RealAPSP
