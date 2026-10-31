-- Prove2me | Theorems.Thm_TestScoreSubmod_overlay_inequality
-- name    : TestScoreSubmod.overlay_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:52.445752+00:00
-- url     : https://prove2.me/theorems/fad60563-c6a9-493a-a842-bd12c6b0e6f4
-- title:
--   Inequalities (22)–(23) inside $n$ coordinates: $g(M_Rx)\le g(z)+\sum_{i\in R}(g(z,x_i)-g(z))$
-- statement:
--   Let $g:\mathbb R_+^n\to\mathbb R$, $n=m+1$, be symmetric, monotone and submodular. For $z\in\mathbb R_+^{n-1}$, $t\in\mathbb R_+$ write $g(z,t)$ for $g$ at $z$ extended by the coordinate $t$, and $g(z)=g(z,0)$. Then for every performance vector $x\in\mathbb R_+^n$ and every set $R$ of items,
--
--   $$
--   g(M_R(x))\le g(z)+\sum_{i\in R}\bigl(g(z,x_i)-g(z)\bigr).
--   $$
--
--   In the paper, $z$ is the performance vector of a fictitious set $S^*$ of $n-1$ items, and (22)–(23) bound $u(S)$ by $u(S^*)$ plus the marginal values $u(S^*\cup\{i\})-u(S^*)$. Taking expectations of this inequality over $x=X$ is that bound; it reduces the upper bound of Lemma 4 to single-item marginals.
--
--   Differences from the source:
--
--   - reading: u(S) ≤ u(S* ∪ S) ≤ u(S*) + Σᵢ (u(S* ∪ {i}) − u(S*)) for a fictitious set S* of n − 1 items with deterministic performances z → the pointwise inequality g(M_R x) ≤ g(z, 0) + Σ_{i∈R} (g(z, xᵢ) − g(z, 0)) inside n coordinates; reason: S* ∪ S has n − 1 + k items, on which g (a function of n coordinates) is not defined (footnote 6, p.35 concedes the abuse); the expectation of this inequality over x = X is what (22)–(23) assert
--   - generalization: z from (21), R = S with |S| = k, g ≥ 0 with extended diminishing returns → every z ∈ ℝ₊ⁿ⁻¹, every R ⊆ N; no nonnegativity or extended diminishing returns; reason: not used; the Lean statement specializes to the source's
--   - reading: φ, "a minimal element which does not change the function value" (p.11) → φ = 0 (mask, pad); reason: p.11 uses φ = 0 and the domain is ℝ₊; with φ > 0 and Xᵢ < φ possible u is not monotone, and if Xᵢ ≥ φ the shift g(x + φ) reduces to φ = 0
--   - encoding: N = {1,…,n}; g(z, t) for z of dimension n − 1 → items Fin (m + 1) (n = m + 1); g (Fin.snoc z t), with g(z) = g (Fin.snoc z 0); reason: n ≥ 1 is forced by 0 < k ≤ n; the new coordinate is the last one, and its position is irrelevant for a symmetric g
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Appendix D, proof of the upper bound of Lemma 4, (22)–(23), p.37

import Mathlib
import Definitions.Def_TestScoreSubmod_IsSubmodularValue
import Definitions.Def_TestScoreSubmod_IsSymmetricValue
import Definitions.Def_TestScoreSubmod_mask

open scoped NNReal

namespace TestScoreSubmod

/-- **Inequalities (22)–(23), inside `n` coordinates** (Sekar, Vojnovic, Yun,
arXiv:1605.07172v4, Appendix D, proof of the upper bound of Lemma 4, (22)–(23), p.37:
"u(S) ≤ u(S* ∪ S) ≤ u(S*) + Σᵢ (u(S* ∪ {i}) − u(S*))").

Let `g : ℝ₊ⁿ → ℝ` (`n = m + 1`) be symmetric, monotone and submodular, `z ∈ ℝ₊^{n−1}`,
`x ∈ ℝ₊ⁿ` and `R ⊆ N`. Then

`g(M_R x) ≤ g(z) + Σ_{i∈R} (g(z, xᵢ) − g(z))`,

where `g(z, t)` is `g` at `z` extended by the coordinate `t` and `g(z) = g(z, 0)`.

**Formalization Note** In the paper `S*` is a fictitious set of `n − 1` items with deterministic
performances `z`, so `S* ∪ S` has `n − 1 + k` items, on which the given `g` (a function of `n`
coordinates) is not defined. Taking expectations of this pointwise inequality over `x = X` is
what (22)–(23) assert. `g(z, t)` is `g (Fin.snoc z t)`, `φ = 0`. -/
theorem overlay_inequality {m : ℕ} (g : (Fin (m + 1) → ℝ≥0) → ℝ)
    (hsym : IsSymmetricValue g) (hmono : Monotone g) (hsub : IsSubmodularValue g)
    (z : Fin m → ℝ≥0) (x : Fin (m + 1) → ℝ≥0) (R : Finset (Fin (m + 1))) :
    g (mask R x) ≤
      g (Fin.snoc (α := fun _ => ℝ≥0) z 0) +
        ∑ i ∈ R, (g (Fin.snoc (α := fun _ => ℝ≥0) z (x i)) -
          g (Fin.snoc (α := fun _ => ℝ≥0) z 0)) := by sorry

end TestScoreSubmod
