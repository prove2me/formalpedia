-- Prove2me | Theorems.Thm_SoftmaxAttnFD_proposition_5_1
-- name    : SoftmaxAttnFD.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:17.782913+00:00
-- url     : https://prove2.me/theorems/2459ea94-9a48-4c72-bd48-7bf24b8ce938
-- title:
--   Proposition 5.1, p.20 — exact maxima in $\tilde O(F_d(m,n))$
-- statement:
--   For fixed $d\ge2$, there are a program and constants $C>0$, $K$ such that for all rational queries $q_i\in\mathbb Q^d$ and points $k_j\in\mathbb Q^d$, the program computes every maximum $M_i=\max_jq_i\cdot k_j$ and a maximizing index, as a Las Vegas algorithm with expected bit cost at most
--   $$C\,F_d(m,n)\,\bigl(b+\log_2(m+n)+\log_2U\bigr)^K.$$
--   For $d\le3$, the same program has no coin instruction and has bit cost at most $C(m+n)(b+\log_2(m+n)+\log_2U)^K$.
--
--   Differences from the source:
--   - encoding: "A Las Vegas algorithm computes … in expected time Õ(F_d(m, n)). For d ≤ 3, the algorithm is deterministic and runs in Õ(m + n) time" → one program of the logarithmic-cost RAM on the batch maxima layout; budget with base b + log₂(m+n) + log₂U; m, n, U ≥ 1; reason: the page names no machine (Machine); U is a magnitude bound and not an input
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Proposition 5.1, p.20

import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_SoftmaxAttnFD_F
import Definitions.Def_SoftmaxAttnFD_BatchMaxima

namespace SoftmaxAttnFD

/-- **Proposition 5.1** (arXiv:2611.06055, sha256 a60f7609…, p.20). For fixed `d ≥ 2`, a Las Vegas
algorithm computes every maximum `M_i = max_j q_i·k_j` and a maximizing index in expected time
`Õ(F_d(m, n))`. For `d ≤ 3`, the algorithm is deterministic and runs in `Õ(m + n)` time.

**Formalization Note** The same program satisfies both clauses, as "the algorithm" says. `U` is a
magnitude bound and is not an input. -/
theorem proposition_5_1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ (P : TimeSpaceMA.Program) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (m n : ℕ) (q : Fin m → Fin d → RatEnc) (k : Fin n → Fin d → RatEnc) (U b : ℕ),
        1 ≤ m → 1 ≤ n → 1 ≤ U → MatBounded q U b → MatBounded k U b →
        LasVegasWithin P (memOf (maxInput q k)) (maxGood q k)
          (C * F d m n * lamMax b m n U ^ K) ∧
        (d ≤ 3 → DeterministicWithin P (memOf (maxInput q k)) (maxGood q k)
          (C * ((m : ℝ) + n) * lamMax b m n U ^ K)) := by sorry

end SoftmaxAttnFD
