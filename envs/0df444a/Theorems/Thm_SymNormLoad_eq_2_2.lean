-- Prove2me | Theorems.Thm_SymNormLoad_eq_2_2
-- name    : SymNormLoad.eq_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:32:10.742201+00:00
-- url     : https://prove2.me/theorems/221096eb-6d29-4f33-92a7-18260862e5a1
-- title:
--   Eq. (2.2) — the load transform $h$ is well defined
-- statement:
--   Let $M\ge2$, $\Psi$ a monotone symmetric norm on $\mathbb R^M$, $\varphi$ the piecewise-linear extension of $k\mapsto\Psi(\mathbf 1_k)$ and $c=\ln(3/2)$. The initial value problem
--   $$
--   h(0)=0,\qquad h'(t)=c\,\varphi\bigl(M e^{-h(t)}\bigr)\quad(t\ge0)
--   $$
--   has a solution on $[0,\infty)$, and any two solutions agree on $[0,\infty)$.
--
--   The paper defines the load transform $h$ by this equation; this statement makes explicit that the definition is meaningful, so that every later result about "the" transform $h$ is about a function that exists and is unique.
--
--   Differences from the source:
--   - encoding: "Define the load transform h : [0, ∞) → [0, ∞) by the following differential equation" (2.2) → existence of h : ℝ → ℝ with IsLoadTransform Ψ h, and any two such agree on [0, ∞); reason: the definition presupposes a unique solution; the item states that presupposition, which the paper uses without proof
--   - encoding: h′(t) on [0, ∞) → HasDerivWithinAt h … (Set.Ici 0) t for every t ≥ 0; reason: two-sided derivative for t > 0, right derivative at the endpoint 0; values on t < 0 unconstrained
--   - encoding: a monotone symmetric norm Ψ : ℝ^M → ℝ≥0 with machines 1, …, M → a function Ψ : (Fin M → ℝ) → ℝ with IsMonotoneSymmetricNorm Ψ (norm axioms, permutation invariance, monotonicity on the orthant); machines 0, …, M−1; reason: Lean convention; the same norms, relabelled coordinates
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Section 2.1.2, Eq. (2.2), p.10

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_IsLoadTransform

namespace SymNormLoad

/-- **Eq. (2.2): the load transform `h` is well defined.** Chen–Im–Sirri, *Online Load Balancing
under Symmetric Norms*, manuscript (STOC 2027 submission), §2.1.2, Eq. (2.2), p.10: "Define the
load transform `h : [0, ∞) → [0, ∞)` by the following differential equation: `h(0) = 0`,
`h′(t) = c φ(r(t))`, `r(t) = M exp(−h(t))`, `c = ln(3/2)`."

The definition presupposes that (2.2) has exactly one solution on `[0, ∞)`. This item states
that: a solution exists, and any two solutions agree on `[0, ∞)`.

**Formalization Note** A solution is `IsLoadTransform Ψ h` (derivative within `[0, ∞)`, so the
right derivative at `0`); uniqueness is on `[0, ∞)` only, since values for `t < 0` are
unconstrained. `2 ≤ M` is the standing assumption of §1.1. -/
theorem eq_2_2 (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) :
    (∃ h : ℝ → ℝ, IsLoadTransform Ψ h) ∧
      ∀ h₁ h₂ : ℝ → ℝ, IsLoadTransform Ψ h₁ → IsLoadTransform Ψ h₂ →
        Set.EqOn h₁ h₂ (Set.Ici 0) := by sorry

end SymNormLoad
