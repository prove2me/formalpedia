-- Prove2me | Theorems.Thm_StretchDepth_Supplement_theorem_3
-- name    : StretchDepth.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:12:24.512087+00:00
-- url     : https://prove2.me/theorems/e03c51f5-f3b3-48bd-a53d-f6c50ba06e2a
-- title:
--   Theorem 3 — Avoid stretch amplification needs $M\le(m+O(\log qd))(N/(n-\log 8q^3))^d$
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $(H,\mathrm{Solve})$ be a $(q,d)$ stretch amplification reduction for Avoid from $n\mapsto N$ stretch to $m\mapsto M$ stretch ($N>n$, $M>m$), where $q\ge2$, $d\ge1$ and $8q^3<2^n$. Then
--   $$
--   M\le\big(m+C\log_2(qd)\big)\left(\frac{N}{n-\log_2(8q^3)}\right)^{d}.
--   $$
--
--   Thus amplifying the stretch of an Avoid instance from $N-n$ to $M-m$ with a solver of $\mathbf{FP^{NP}}$ complexity $q$ requires adaptivity depth $d$ of order $\log(M/m)/\log(N/n)$.
--
--   **Formalization Note** The denominator is positive because $8q^3<2^n$. $\mathrm{Solve}$ has complexity $q$ in both senses (at most $q$ DNF queries, each of width at most $q$) and no depth restriction.
--
--   Differences from the source:
--   - reading: $O(\log(qd))$ with an unspecified constant → one constant $C>0$ fixed before all parameters, $\log=\log_2$; reason: the universal-constant reading of the base goal, Theorem 1.
--   - reading: "$Q^G$ proceeds in $q$ phases" → at most $q$ NP-queries on every run; reason: a procedure can pad with dummy queries, so the class is the same.
--   - encoding: the query and width bounds of $\mathrm{Solve}$ and $H$ → imposed on the runs against actual functions $G$; reason: branches no $G$ reaches are never executed, so the reductions are the same.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Theorem 3, p.18 (PDF p.18)

import Definitions.Def_StretchDepth_Supplement_IsAvoidReduction

set_option autoImplicit false

namespace StretchDepth.Supplement

/-- **Theorem 3: the depth lower bound for stretch amplification of Avoid.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Theorem 3, p.18: "Let (H, Solve) be a (q, d) stretch amplification reduction for
Avoid from n ↦ N stretch to m ↦ M stretch, where q ≥ 2, d ≥ 1, and 8q³ < 2ⁿ. Then
M ≤ (m + O(log(qd))) (N/(n − log(8q³)))^d."

**Formalization Note.** The constant of `O(log(qd))` is universal, so it comes before the instance;
`log = log₂`. The denominator `n − log₂(8q³)` is the page's, with no constant; it is positive
because `8q³ < 2ⁿ`. The conditions `N > n`, `M > m` of Definition 6 are binders. `Solve` has
complexity `q` in both senses (at most `q` NP-queries, each a DNF of width at most `q`) and no
depth restriction; `H` is not assumed free of repeated queries. -/
theorem theorem_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n N m M q d : ℕ) (H : Bits m → RoundTree n N M) (Solve : Bits M → FPNPProc n N),
        n < N → m < M → 2 ≤ q → 1 ≤ d → 8 * q ^ 3 < 2 ^ n →
        IsAvoidReduction H Solve q d →
        (M : ℝ) ≤ ((m : ℝ) + C * Real.logb 2 ((q : ℝ) * d)) *
          ((N : ℝ) / ((n : ℝ) - Real.logb 2 (8 * (q : ℝ) ^ 3))) ^ d := by sorry

end StretchDepth.Supplement
