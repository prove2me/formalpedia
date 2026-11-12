-- Prove2me | Theorems.Thm_SuccinctArgOWF_Kilian_selective_implies_adaptive
-- name    : SuccinctArgOWF.Kilian.selective_implies_adaptive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:30.642052+00:00
-- url     : https://prove2.me/theorems/f993dd67-5f22-4e30-b988-8679ee2ee8e9
-- title:
--   Proposition 3.6 — selective implies adaptive binding
-- statement:
--   Let $\mathrm{Com}$ be a public-coin commitment scheme with interval opening for messages in $\{0,1\}^N$ and $t\in\mathbb N$. For one universal constant $C$, every adversary of running time at most $t$
--
--   1. wins the adaptive interval binding game with probability at most $\binom{N+1}{2}\cdot\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}}\bigl(t+C(\log N+1)\bigr)$, and
--   2. wins the adaptive position binding game with probability at most $N\cdot\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}}\bigl(t+C(\log N+1)\bigr)$.
--
--   Since $\binom{N+1}{2}\le N^2$, this gives the printed bounds
--
--   $$O(N^2)\cdot\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}}(t+O(\log N))\quad\text{and}\quad N\cdot\mathrm{bind}^{\mathrm{int}}_{\mathrm{Com}}(t+O(\log N)).$$
--
--   It converts the selective binding of Corollary 6.3 into adaptive position binding.
--
--   **Formalization Note** $\log N$ is $\lfloor\log_2N\rfloor$.
--
--   Differences from the source:
--   - generalization: O(N²) → the factor binom(N+1, 2) ≤ N², the number of intervals (from the proof); reason: a sharper explicit factor implies the printed O(N²)
--   - encoding: t + O(log N) → t + C·(⌊log₂ N⌋ + 1) with one constant C chosen before Com, t and the adversary; reason: the +1 covers N = 1; for N ≥ 2 the two forms agree up to the constant
--   - reading: non-uniform probabilistic Turing machines with a fixed binary encoding; running time = worst-case steps + description + advice → one machine of the published MetaSearch model with advice per phase of the game, a random tape of length t, cost = total steps + codes and advice of the distinct phase programs, worst case over all coins and all inputs the game can give; reason: the paper fixes no model; a single machine for all phases is the special case
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Proposition 3.6, p. 9 (PDF p. 11)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Commit

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-- Proposition 3.6 (selective implies adaptive binding), Dujmovic–Wichs p.9. For a universal
constant `C`, every public-coin commitment with interval opening for `{0,1}^N`, every `t` and every
adversary of running time at most `t`: it wins the adaptive interval binding game with probability at
most `binom(N+1, 2) · bind^int_Com(t + C(log N + 1))` and the adaptive position binding game with
probability at most `N · bind^int_Com(t + C(log N + 1))`. -/
theorem selective_implies_adaptive :
    ∃ C : ℕ, ∀ (Com : ICommit) (t : ℕ) (A : Adv),
      A.RunsWithin t [] (Set.range Com.adaSched) →
        Com.adaProb false A t ≤
            ((Com.N + 1).choose 2 : ℝ) * Com.bindInt (t + C * (Nat.log 2 Com.N + 1)) ∧
          Com.adaProb true A t ≤ (Com.N : ℝ) * Com.bindInt (t + C * (Nat.log 2 Com.N + 1)) := by sorry

end SuccinctArgOWF.Kilian
