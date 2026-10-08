-- Prove2me | Theorems.Thm_SethiChengSS_Finite_theorem_3_1_dp_C1
-- name    : SethiChengSS.Finite.theorem_3_1_dp_C1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:41.415911+00:00
-- url     : https://prove2.me/theorems/e361c535-747b-4cd7-9c1e-c4350d720b94
-- title:
--   Theorem 3.1 (first part), p. 933 — the dynamic programming equations (3.2) define functions in C_1
-- statement:
--   Consider the Markov-modulated inventory model of Sethi and Cheng under the standing assumptions of §2. Let $v_N, v_{N-1}, \dots, v_0$ be the functions defined by the dynamic programming equations (3.2):
--   $$v_N(i,x) = f_N(i,x), \qquad v_n(i,x) = f_n(i,x) + \inf_{u \ge 0}\big\{c_n(i,u) + F_{n+1}(v_{n+1})(i,x+u)\big\}.$$
--   Then every $v_n$, $n \in \langle 0, N\rangle$, belongs to $C_1$:
--   1. it is nonnegative and a pointwise limit of nonnegative continuous functions;
--   2. it has linear growth, $v_n(i,x) \le C_n(1+|x|)$ for some $C_n > 0$;
--   3. it is uniformly continuous in $x$ for each demand state $i$.
--
--   This regularity makes every expectation in the recursion finite and allows the later sections to work with continuous cost-to-go functions.
--
--   **Formalization Note** This is the first sentence of Theorem 3.1 and uses only the §2 assumptions. In Lean the recursion uses Bochner integrals and real infima, which return junk values on non-integrable integrands or unbounded sets. This theorem shows that neither case occurs.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 933, Theorem 3.1 (first sentence)

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
import Definitions.Def_SethiChengSS_Finite_Model
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SethiChengSS.Finite

/-- Theorem 3.1, first sentence (Sethi–Cheng 1997, p. 933): under the standing assumptions of §2,
the dynamic programming equations (3.2) define functions `v_n`, `n ∈ ⟨0, N⟩`, in `C_1`. -/
theorem theorem_3_1_dp_C1 {L : ℕ} (D : Data L) (N : ℕ) (hS : Standing D) :
    ∀ n ≤ N, InC1 (dpV D N n) := by sorry

end SethiChengSS.Finite
