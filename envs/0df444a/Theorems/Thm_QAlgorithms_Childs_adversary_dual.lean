-- Prove2me | Theorems.Thm_QAlgorithms_Childs_adversary_dual
-- name    : QAlgorithms.Childs.adversary_dual
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:33:58.878872+00:00
-- url     : https://prove2.me/theorems/ff8bea57-2967-4e01-a1be-3b4e1d6be1fd
-- title:
--   The dual of the general adversary bound
-- statement:
--   Let $S \subseteq \{0,1\}^n$ and let $f : S \to \{0,1\}$ be a (possibly partial) Boolean function. An adversary matrix for $f$ is a real symmetric matrix $\Gamma \in \mathbb{R}^{|S|\times|S|}$ with $\Gamma_{xy} = 0$ whenever $f(x) = f(y)$; for $i \in [n]$, $\Gamma_i$ is the matrix with $(\Gamma_i)_{xy} = \Gamma_{xy}$ if $x_i \ne y_i$ and $0$ otherwise. The general (negative-weights) adversary bound is
--
--   $$\mathrm{Adv}^{\pm}(f) = \max_{\Gamma} \frac{\|\Gamma\|}{\max_{i\in[n]} \|\Gamma_i\|},$$
--
--   with spectral norms. For a positive integer $d$ and vectors $|v_{x,i}\rangle \in \mathbb{C}^d$ ($x \in S$, $i \in [n]$), define the $b$-complexity $C_b = \max_{x \in f^{-1}(b)} \sum_{i\in[n]} \||v_{x,i}\rangle\|^2$ for $b \in \{0,1\}$. Call the family feasible if
--
--   $$\sum_{i : x_i \ne y_i} \langle v_{x,i} | v_{y,i} \rangle = 1 - \delta_{f(x),f(y)} \quad \text{for all } x \ne y \text{ in } S.$$
--
--   Then
--
--   $$\mathrm{Adv}^{\pm}(f) = \min \max\{C_0, C_1\},$$
--
--   the minimum over all positive integers $d$ and all feasible families; in particular the minimum is attained.
--
--   This strong-duality statement turns the adversary lower bound into a minimization, so that explicit dual solutions give upper bounds on $\mathrm{Adv}^{\pm}(f)$ and, via the algorithm of §24.6, on quantum query complexity.
--
--   **Formalization Note** The index set $[n]$ is an arbitrary finite type. $\mathrm{Adv}^{\pm}(f)$ is the supremum, in $[0,\infty]$, of the ratio over nonzero adversary matrices, and is $0$ when $f$ is constant on $S$ (then $\Gamma = 0$ is the only adversary matrix and the source's ratio is $0/0$). An empty maximum $C_b$ is $0$. The minimum is stated as: the value is attained by a feasible family and bounds every feasible objective from below.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 124, Theorem 24.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Adversary
set_option autoImplicit false

namespace QAlgorithms.Childs

open scoped NNReal ENNReal

/-- Childs, Theorem 24.1 (PDF p. 124): the dual of the general adversary bound. For any
`f : S → {0,1}` with `S ⊆ {0,1}^n`, `Adv±(f) = min max{C₀, C₁}`, the minimum over all positive
integers `d` and all families of vectors `|v_{x,i}⟩ ∈ ℂ^d` (`x ∈ S`, `i ∈ [n]`) satisfying
(24.3): `∑_{i : x_i ≠ y_i} ⟨v_{x,i}|v_{y,i}⟩ = 1 − δ_{f(x),f(y)}` for all `x ≠ y`, where
`C_b = max_{x ∈ f⁻¹(b)} ∑_i ‖|v_{x,i}⟩‖²`. "Min" is rendered as `IsLeast`: the value is attained
by a feasible family and is a lower bound on every feasible objective. -/
theorem adversary_dual {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool)
    (D : Finset (ι → Bool)) :
    IsLeast {r : ℝ≥0∞ | ∃ (d : ℕ) (v : D → ι → EuclideanSpace ℂ (Fin d)), 0 < d ∧
        DualFeasibleChilds f D d v ∧ r = (childsDualObjective f D v : ℝ≥0∞)}
      (advPm f D) := by
  sorry



end QAlgorithms.Childs
