-- Prove2me | Theorems.Thm_StretchDepth_Supplement_theorem_7
-- name    : StretchDepth.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:14:02.723223+00:00
-- url     : https://prove2.me/theorems/68f8b65f-d304-42e9-a909-4f1b5bfb8e5b
-- title:
--   Theorem 7 — the depth bound $M\le(m+O(\log qd))(N/(n-O(\log(q/\epsilon))))^d$ for reductions with advice
-- statement:
--   There are universal constants $c,C_1,C_2>0$ such that the following holds. Let $(H,R)$ be a $(q,0.9,\epsilon,d)$ amplification reduction with nonuniform security from $n\mapsto N$ stretch to $m\mapsto M$ stretch ($N>n$, $M>m$), where $q\ge2$, $d\ge1$, $0<\epsilon\le1$ and $q,\epsilon^{-1}\le2^{cn}$. Then $n-C_2\log_2(q/\epsilon)>0$ and
--   $$
--   M\le\big(m+C_1\log_2(qd)\big)\left(\frac{N}{n-C_2\log_2(q/\epsilon)}\right)^{d}.
--   $$
--
--   This extends the mission's goal (Theorem 1) to security reductions that receive $q$ bits of advice depending on the generator $G$ and the test $T$.
--
--   **Formalization Note** The constants are not tied to those of Theorem 1.
--
--   Differences from the source:
--   - reading: $c$ and the two $O(\cdot)$ → constants $c,C_1,C_2>0$ fixed before the instance, $\log=\log_2$; reason: the universal-constant reading of the base goal, Theorem 1.
--   - encoding: the bound alone → the bound together with $n-C_2\log_2(q/\epsilon)>0$; reason: it follows by taking $c$ small, and a nonpositive denominator would make the bound meaningless in Lean.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Appendix A, Theorem 7, p.31 (PDF p.31)

import Definitions.Def_StretchDepth_Supplement_IsNonuniformReduction

set_option autoImplicit false

namespace StretchDepth.Supplement

/-- **Theorem 7: the depth lower bound for amplification reductions with nonuniform security.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Appendix A, Theorem 7, p.31: "There is a universal constant c > 0 such that the
following holds. Let (H, R) be a (q, 0.9, ϵ, d) amplification reduction with nonuniform security
from n ↦ N stretch to m ↦ M stretch, where q ≥ 2, d ≥ 1, 0 < ϵ ≤ 1, and q, ϵ⁻¹ ≤ 2^{cn}. Then
M ≤ (m + O(log(qd))) (N/(n − O(log(q/ϵ))))^d."

**Formalization Note.** Read exactly as the base goal `StretchDepth.theorem_1`: `c` and the
constants of the two `O(·)` are universal and come before the instance (they are not tied to
Theorem 1's); `log = log₂`; the conclusion also states `0 < n − C₂ log₂(q/ϵ)`. The conditions
`N > n`, `M > m` of Definition 7 are binders; `γ = 0.9` is `9/10`. The advice `a ∈ {0,1}^q` may
depend on `G` and `T`; every `R_a` makes at most `q` queries. -/
theorem theorem_7 :
    ∃ c C₁ C₂ : ℝ, 0 < c ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (n N m M q d : ℕ) (ε : ℝ) (H : Bits m → RoundTree n N M)
        (R : Bits q → PMF (Bits N → QProc n N M)),
        n < N → m < M → 2 ≤ q → 1 ≤ d → 0 < ε → ε ≤ 1 →
        (q : ℝ) ≤ (2 : ℝ) ^ (c * n) → ε⁻¹ ≤ (2 : ℝ) ^ (c * n) →
        IsNonuniformReduction H q R (9 / 10) ε d →
        0 < (n : ℝ) - C₂ * Real.logb 2 ((q : ℝ) / ε) ∧
          (M : ℝ) ≤ ((m : ℝ) + C₁ * Real.logb 2 ((q : ℝ) * d)) *
            ((N : ℝ) / ((n : ℝ) - C₂ * Real.logb 2 ((q : ℝ) / ε))) ^ d := by sorry

end StretchDepth.Supplement
