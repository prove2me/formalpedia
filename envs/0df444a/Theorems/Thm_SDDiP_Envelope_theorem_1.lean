-- Prove2me | Theorems.Thm_SDDiP_Envelope_theorem_1
-- name    : SDDiP.Envelope.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:45:04.050157+00:00
-- url     : https://prove2.me/theorems/363b3cc0-acd9-4ed4-9d63-a4449e413a8a
-- title:
--   Theorem 1 — the convex lower envelope of $f$ on $\{0,1\}^n$ is convex piecewise linear on $[0,1]^n$ and equals $f$ at binary points
-- statement:
--   Let $n \ge 0$ and let $f$ be a real valued function defined on $\{0,1\}^n$. Then $f$ has a convex lower envelope $e$ in the sense of Definition 3 (the largest function that is convex on $\operatorname{conv}(\{0,1\}^n)$ and majorized by $f$ on $\{0,1\}^n$), and every convex lower envelope $e$ of $f$ satisfies:
--
--   1. $e$ is convex on $[0,1]^n$;
--   2. $e$ is piecewise linear on $[0,1]^n$ with finitely many pieces: there are $K \in \mathbb N$, $\alpha_1,\dots,\alpha_K \in \mathbb R^n$ and $\beta_1,\dots,\beta_K \in \mathbb R$ with
--   $$e(x) = \max_{k=1,\dots,K}\big(\alpha_k^\top x + \beta_k\big) \qquad \text{for all } x \in [0,1]^n;$$
--   3. $e$ coincides with $f$ at all binary points: $e(x) = f(x)$ for every $x \in \{0,1\}^n$.
--
--   The theorem says that any real function of binary variables is represented exactly by a convex polyhedral function on the cube. It is the reason value functions of multistage stochastic integer programs with binary state variables admit exact, tight convex polyhedral cut approximations, on which the SDDiP algorithm rests.
--
--   **Formalization Note** The convex lower envelope is defined as a predicate (Definition 3), so the theorem asserts its existence and then the three properties for every function satisfying it; all of them agree on $[0,1]^n$. $f$ is a total function on $\mathbb R^n$ of which only the values at binary points matter. The maximum of affine functions is written as: each is $\le e(x)$ and one equals $e(x)$.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 467, Theorem 1 (definitions: p. 496, Definition 3)

import Mathlib
import Definitions.Def_SDDiP_Envelope_ConvexLowerEnvelope

namespace SDDiP.Envelope

/-- **Theorem 1** (Zou, Ahmed, Sun, *Stochastic dual dynamic integer programming*, Math. Program. 175
(2019), p. 467). Let `f` be a real valued function on `{0,1}ⁿ`. Then `f` has a convex lower envelope
(Definition 3 with `X = {0,1}ⁿ`), and every convex lower envelope `e` of `f` is a convex piecewise
linear function on `[0,1]ⁿ` (the maximum of finitely many affine functions there) and coincides with
`f` at all binary points. -/
theorem theorem_1 (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (∃ e : (Fin n → ℝ) → ℝ, IsConvexLowerEnvelope (binaryPoints n) f e) ∧
    ∀ e : (Fin n → ℝ) → ℝ, IsConvexLowerEnvelope (binaryPoints n) f e →
      ConvexOn ℝ (cube n) e ∧ IsMaxOfAffineOn (cube n) e ∧
      ∀ x ∈ binaryPoints n, e x = f x := by sorry

end SDDiP.Envelope
