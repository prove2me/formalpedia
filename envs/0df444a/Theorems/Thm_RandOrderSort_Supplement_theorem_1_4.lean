-- Prove2me | Theorems.Thm_RandOrderSort_Supplement_theorem_1_4
-- name    : RandOrderSort.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:02:00.927094+00:00
-- url     : https://prove2.me/theorems/ca99b09b-534e-464c-b3bc-7f5cb621564c
-- title:
--   Theorem 1.4 — for every randomized online algorithm a fixed set of $n$ distinct values in $[0,1]$ has $\rho<c_0\log n$ in random order with probability at most $4e^{-c_1\sqrt n}$
-- statement:
--   There are absolute constants $c_0,c_1>0$ and $n_0$ such that the following holds for every $n\ge n_0$ and every randomized measurable online algorithm $A$ with full access to the numerical values that uses exactly $n$ cells, with internal random tape $\zeta\sim\mu$. There is a fixed set $X=\{x_1,\dots,x_n\}\subset[0,1]$ of $n$ distinct values such that, when $X$ is presented in the order of a uniform random permutation $\pi$ of $[n]$, independent of $\zeta$,
--
--   $$\mathbb P_{\pi,\zeta}\bigl[\rho(A(X_\pi))<c_0\log n\bigr]\le 4e^{-c_1\sqrt n},$$
--
--   where $X_\pi=(x_{\pi(1)},\dots,x_{\pi(n)})$ and $\rho=\mathrm{cost}/\mathrm{OPT}(X)$ is the realized competitive ratio of display (1). The set may depend on $A$ and $n$ but is fixed before the permutation and the tape are drawn.
--
--   Together with Theorem 1.1 this shows that the optimal worst-case competitive ratio of online sorting in random order is $\Theta(\log n)$ with high probability.
--
--   **Formalization Note** The set is a vector $x:\mathrm{Fin}\,n\to\mathbb R$, injective with values in $[0,1]$; the stream is $x\circ\pi$. The joint probability over independent $\pi$ and $\zeta$ is written as $\frac1{n!}\sum_\pi\mu\{\zeta:\rho<c_0\log n\}$.
--
--   Differences from the source:
--   - reading: "For every n ≥ n0 … c0 … c1" (the constants of Theorem 1.3) → the theorem carries its own prefix ∃ c0 c1 > 0, ∃ n0, chosen before n and A; reason: the statement then stands alone; any triple valid for Theorem 1.3 is valid here by the proof (p.43), and the paper's form follows from the two items with the paper's explicit constants.
--   - encoding: "every such online algorithm" → a RandOnlineAlg satisfying LegalOn n; reason: same class as Theorem 1.3, containing every algorithm of the page.
--   - encoding: tape space of arbitrary size → a type in a fixed but arbitrary universe u; reason: Lean cannot quantify over universes.
--   - encoding: P_{π,ζ} with π uniform and independent of ζ → (1/n!) ∑_π μ{ζ : ρ(A; x∘π, ζ) < c0 log n} in ℝ≥0∞; reason: the product of the uniform law on permutations and μ, by Fubini over the finite factor.
--   - encoding: fixed set X of n distinct values → an injective vector x : Fin n → ℝ with values in [0,1]; reason: the indices only name the elements.
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Theorem 1.4, p.4; display (1), p.3; proof §5.1.4, p.43

import Mathlib
import Definitions.Def_RandOrderSort_Supplement_RandOnlineAlg

namespace RandOrderSort

namespace Supplement

open MeasureTheory

universe u

/-- **Theorem 1.4 (Lower tail in random order)**, Kang, Fan, arXiv:2610.15438 (version of
2026-11-01), p.4: "For every n ≥ n0 and every such online algorithm A, there is a fixed set
X ⊂ [0, 1] of n distinct values such that P_{π,ζ}[ρ(A(X_π)) < c0 log n] ≤ 4e^{−c1√n}. The set may
depend on A and n, but is fixed before the permutation and the independent algorithmic tape are
drawn."

**Formalization Note.** The constants are stated with their own existential prefix, chosen before
`n` and the algorithm. The set is `x : Fin n → ℝ`, injective with values in `[0,1]`, chosen after
`A` and `n` and before `π` and `ζ`. The stream is `x ∘ π` (arrival `t` has value `x (π t)`). The
probability over independent `π` (uniform on the `n!` permutations) and `ζ ~ μ` is written as the
average over `π` of the tape probability, which is the product measure by Fubini. `ρ` is
display (1); `log` is the natural logarithm. -/
theorem theorem_1_4 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ A : RandOnlineAlg.{u}, A.LegalOn n →
        ∃ x : Fin n → ℝ, Function.Injective x ∧ (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧
          (∑ π : Equiv.Perm (Fin n),
              A.μ {ζ : A.Ω | A.ratio ζ (x ∘ π) < c₀ * Real.log n}) /
              (Fintype.card (Equiv.Perm (Fin n)) : ENNReal) ≤
            ENNReal.ofReal (4 * Real.exp (-(c₁ * Real.sqrt n))) := by sorry

end Supplement

end RandOrderSort
