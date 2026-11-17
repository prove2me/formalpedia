-- Prove2me | Theorems.Thm_QLocalCert_Supplement_theorem_5
-- name    : QLocalCert.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:40:31.605229+00:00
-- url     : https://prove2.me/theorems/ceb71177-a8cc-4d66-9c80-d56190f9e939
-- title:
--   Theorem 5 — equality on a path: one-round dQMA with $O(\min\{r\log N,\,N^{2/3}(\log N)^{5/3}\})$ certificate qubits per node
-- statement:
--   There is a constant $C$ such that for every input length $N\ge 2$ and every path $v_0,\dots,v_r$ of length $r\ge1$ there is a one-round dQMA protocol (Definition 18) for $\mathrm{EQ}^2_N$, the equality of the $N$-bit strings $x$ held at $v_0$ and $y$ held at $v_r$, such that:
--
--   1. **perfect completeness:** for every $x$ some certificate state is accepted on $(x,x)$ with probability $1$;
--   2. **soundness:** for $x\ne y$ every certificate state, arbitrarily entangled across the nodes, is accepted with probability at most $1/3$;
--   3. **certificate size:** every node $v_j$ receives
--   $$
--   c(v_j)\le C\cdot\min\big\{\,r\log_2 N,\ N^{2/3}(\log_2 N)^{5/3}\big\}
--   $$
--   qubits.
--
--   The two bounds come from two independent protocols: the first improves the previous $O(r^2\log N)$ bound, the second is independent of the path length. They are used for the bounded-radius and the unrestricted graph-symmetry protocols respectively.
--
--   **Formalization Note** One constant $C$ is chosen before $N$ and $r$; logarithms are base 2. Message sizes are not restricted.
--
--   Differences from the source:
--   - encoding: O(min{r log N, N^{2/3}(log N)^{5/3}}) qubits per node → one constant C before N and r, for all N ≥ 2, r ≥ 1; reason: big-O as one constant; log₂ 1 = 0, so N = 1 only excludes a degenerate case, and finitely many small N are absorbed into C (p.22)
--   - encoding: arbitrary pure prover state (Definition 18) → arbitrary density operator; reason: by convexity the maximal and all worst-case acceptance probabilities are the same
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Theorem 5, p.6; model Definition 18, p.32; proofs Lemma 10, p.21 and §3.2, pp.22–31

import Mathlib
import Definitions.Def_QLocalCert_Supplement_PathDQMA

set_option autoImplicit false

namespace QLocalCert.Supplement

/-- **Theorem 5** (Improved protocols for equality on a path, p.6). "For every path P = v0, . . . , vr
of length r ≥ 1, the problem EQ²_N of two N-bit strings held at the endpoint nodes v0 and vr admits a
one-round dQMA protocol with perfect completeness, soundness error at most 1/3 and certificates of
O(min{r log N, N^{2/3}(log N)^{5/3}}) qubits per node."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Theorem 5, p.6; the protocol model is
Definition 18, p.32; the two bounds are proved by Lemma 10 (p.21) and §3.2 (pp.22–31).

**Formalization Note.**
* The model is `PathDQMA N r` (Definition 18), with certificate sizes `cert j = c(v_j)` per node.
* `O(·)` is one constant `C` chosen before `N` and `r`, valid for all `N ≥ 2` and `r ≥ 1`
  (`log₂ 1 = 0`, so `N = 1` is excluded; finitely many small `N` are absorbed into `C`).
* Perfect completeness: on `x = y` some certificate is accepted with probability `≥ 1`. Soundness
  error `1/3` against every density operator on the joint certificate space. Message sizes are not
  restricted by the statement. `log` is `Real.logb 2`; real powers are `Real.rpow`. -/
theorem theorem_5 :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ r : ℕ, 1 ≤ r → ∃ P : PathDQMA N r,
      (∀ j : ℕ, j ≤ r → (P.cert j : ℝ) ≤
        C * min ((r : ℝ) * Real.logb 2 N)
          ((N : ℝ) ^ ((2 : ℝ) / 3) * Real.logb 2 N ^ ((5 : ℝ) / 3))) ∧
      P.Correct 1 (1 / 3) := by sorry

end QLocalCert.Supplement
