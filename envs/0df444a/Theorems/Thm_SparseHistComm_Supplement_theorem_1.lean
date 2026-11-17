-- Prove2me | Theorems.Thm_SparseHistComm_Supplement_theorem_1
-- name    : SparseHistComm.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:42:56.093765+00:00
-- url     : https://prove2.me/theorems/f91f7171-b6ce-4744-ae82-2f775b93eb26
-- title:
--   Theorem 1 — bounds on $\Lambda_{n,k,D}(\delta)$
-- statement:
--   For every $n\ge1$, $k\ge1$, $0\le D<k$, and $0\le\delta<1$,
--
--   $$
--   (1-\delta)(nk-\lfloor nD\rfloor)
--     \le \Lambda_{n,k,D}(\delta)
--     \le (1-\delta)n(k-\lfloor D\rfloor).
--   $$
--
--   Moreover, there is a universal constant $C>0$ such that, whenever $0<\delta<1$ and $t=nk-\lfloor nD\rfloor\ge\max\{2,1/\delta\}$,
--
--   $$
--   \Lambda_{n,k,D}(\delta)
--     \le (1-\delta)t\left(1+C\sqrt{\frac{\ln t}{t}}\right).
--   $$
--
--   These estimates bound the leading homogeneous communication coefficient by deterministic covering and by a concentrated randomized covering law.
--
--   Differences from the source:
--   - encoding: the universal $O(\sqrt{\ln t/t})$ in (15) → one positive constant $C$ quantified before all parameters; reason: p.14 states that the implied constant is universal, and this is its literal quantifier form
--   - encoding: $nk-\lfloor nD\rfloor$ → the published integer-valued `threshold`, coerced to $\mathbb R$ in analytic expressions; reason: this preserves the real floor of the product $nD$ exactly
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Theorem 1, pp.7–8, (14)–(15); explicit universal bound, p.14

import Mathlib
import Definitions.Def_SparseHistComm_Lambda
import Definitions.Def_SparseHistComm_threshold

namespace SparseHistComm

namespace Supplement

/-- **Theorem 1 (Bounds on the homogeneous coefficient)** (Ye–Fan, *Optimal Communication for
Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256
29df82a4…f27c6f), pp.7–8, (14)–(15)). The constant in (15) is universal, as the explicit
estimate on p.14 shows.

**Formalization Note** `threshold n k D = nk - ⌊nD⌋` is integer-valued and is coerced to `ℝ`
in the displayed bounds. `Real.log` is the paper's natural logarithm in (15). -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) (D δ : ℝ),
      1 ≤ n → 1 ≤ k → 0 ≤ D → D < k → 0 ≤ δ → δ < 1 →
      (1 - δ) * (threshold n k D : ℝ) ≤ Lambda n k D δ ∧
      Lambda n k D δ ≤ (1 - δ) * n * (k - ⌊D⌋) ∧
      (0 < δ → max 2 (1 / δ) ≤ (threshold n k D : ℝ) →
        Lambda n k D δ ≤ (1 - δ) * (threshold n k D : ℝ) *
          (1 + C * Real.sqrt (Real.log (threshold n k D : ℝ) /
            (threshold n k D : ℝ)))) := by sorry

end Supplement

end SparseHistComm
