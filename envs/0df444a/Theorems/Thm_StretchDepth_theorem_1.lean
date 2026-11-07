-- Prove2me | Theorems.Thm_StretchDepth_theorem_1
-- name    : StretchDepth.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:25.108195+00:00
-- url     : https://prove2.me/theorems/adc481ce-95df-4813-a7e6-ad60873e9cfd
-- title:
--   Theorem 1 — $M\le(m+O(\log qd))(N/(n-O(\log(q/\epsilon))))^d$ for black-box PRG stretch amplification
-- statement:
--   There are universal constants $c,C_1,C_2>0$ such that the following holds. Let $n<N$ and $m<M$, and let $(H,R)$ be a $(q,0.9,\epsilon,d)$ PRG amplification reduction from $n\mapsto N$ stretch to $m\mapsto M$ stretch, where $q\ge2$, $d\ge1$, $0<\epsilon\le1$ and $q,\epsilon^{-1}\le2^{cn}$. Then $n-C_2\log_2(q/\epsilon)>0$ and
--   $$
--   M\le\bigl(m+C_1\log_2(qd)\bigr)\Bigl(\frac{N}{n-C_2\log_2(q/\epsilon)}\Bigr)^d.
--   $$
--   So the known composition-based amplification is optimal in depth up to constants among all fully black-box constructions with $d$ adaptive rounds and arbitrary post-processing: for polynomial $q$ and $\epsilon^{-1}$, amplifying $n\mapsto n+1$ to $m\mapsto2m$ needs depth $\Omega(n/\log n)$. The constraint is on the depth of $H$ only: $R$ may be fully adaptive.
--
--   **Formalization Note** $H$ is a family of round trees, and $R$ is a distribution over families of decision trees, so the statement is purely about query complexity, with no machine model and no running time. $H$ is not assumed free of repeated queries.
--
--   Differences from the source:
--   - reading: c > 0 universal, with O(log(qd)) and O(log(q/eps)) → exists c, C1, C2 > 0 before the instance, with log = log_2 and constants C1, C2; reason: the O constants are universal in Theorem 1; a change of log base is absorbed by the constants
--   - reading: the denominator n - O(log(q/eps)) of the printed bound, implicitly positive → an explicit conjunct 0 < n - C2 log_2(q/eps) in the conclusion; reason: it follows by taking c small, since q >= 2 and q, 1/eps <= 2^{cn}; without it a bound with denominator of the wrong sign would have no content
--   - encoding: a randomized query procedure with q queries on every input and all randomness → a PMF over functions to decision trees, with the bound on real pairs (G, T) and on the support; reason: the procedures with at most q queries form a finite set after pruning unreachable branches, and only runs on real pairs matter to the definition
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Theorem 1, p.19

import Definitions.Def_StretchDepth_IsPRGReduction

namespace StretchDepth

/-- **Theorem 1: the depth lower bound for PRG stretch amplification.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Theorem 1, p.19: "There is a universal constant c > 0 such that the following holds. Let
(H, R) be a (q, 0.9, ϵ, d) PRG amplification reduction from n ↦ N stretch to m ↦ M stretch, where
q ≥ 2, d ≥ 1, 0 < ϵ ≤ 1, and q, ϵ−1 ≤ 2cn. Then M ≤ (m + O(log(qd))) (N/(n − O(log(q/ϵ))))^d."

**Formalization Note.** `c` and the constants of the two `O(·)` are universal, so they come before
the instance; `log = log₂`, and the base is absorbed by the constants. The conclusion also states
`0 < n − C₂ log₂(q/ϵ)`: it follows by taking `c` small, and without it a denominator of the wrong
sign or zero would make the bound meaningless in Lean. The conditions `N > n`, `M > m` of
Definition 3 are binders; `γ = 0.9` is `9/10`. `IsPRGReduction` places no bound on `R`'s depth and
`H` is not assumed free of repeated queries. -/
theorem theorem_1 :
    ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (n N m M q d : ℕ) (ε : ℝ) (H : Bits m → RoundTree n N M)
        (R : PMF (Bits N → QProc n N M)),
        n < N → m < M → 2 ≤ q → 1 ≤ d → 0 < ε → ε ≤ 1 →
        (q : ℝ) ≤ (2 : ℝ) ^ (c * n) → ε⁻¹ ≤ (2 : ℝ) ^ (c * n) →
        IsPRGReduction H R q (9 / 10) ε d →
        0 < (n : ℝ) - C₂ * Real.logb 2 ((q : ℝ) / ε) ∧
          (M : ℝ) ≤ ((m : ℝ) + C₁ * Real.logb 2 ((q : ℝ) * d)) *
            ((N : ℝ) / ((n : ℝ) - C₂ * Real.logb 2 ((q : ℝ) / ε))) ^ d := by sorry

end StretchDepth
