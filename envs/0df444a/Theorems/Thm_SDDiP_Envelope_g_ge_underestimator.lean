-- Prove2me | Theorems.Thm_SDDiP_Envelope_g_ge_underestimator
-- name    : SDDiP.Envelope.g_ge_underestimator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:45:58.0221+00:00
-- url     : https://prove2.me/theorems/b6906340-2b6c-4cfe-a981-c555a5eab961
-- title:
--   Proof of Theorem 1, p. 496 — $g \ge h$ on $[0,1]^n$ for every convex underestimator $h$ of $f$
-- statement:
--   Let $f$ be a real function on $\{0,1\}^n$, $g$ as in the proof of Theorem 1, and $h$ a convex underestimator of $f$ in the sense of Definition 3 with $X = \{0,1\}^n$: $h$ is convex on $\operatorname{conv}(\{0,1\}^n)$ and $h(x) \le f(x)$ for every $x \in \{0,1\}^n$. Then
--   $$h(x) \le g(x) \qquad \text{for all } x \in C_n = [0,1]^n.$$
--
--   Together with the facts that $g$ is itself a convex underestimator, this shows that $g$ is the convex lower envelope of $f$.
--
--   **Formalization Note** The inequality is stated on the whole cube, as in the paper's conclusion "g(x) ≥ h(x) for all x ∈ C_n"; the printed argument treats the interior $(0,1)^n$ and the binary points separately.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 496, proof of Theorem 1, last paragraph

import Mathlib
import Definitions.Def_SDDiP_Envelope_ProofLP

namespace SDDiP.Envelope

/-- Proof of Theorem 1, p. 496: `g` dominates every convex underestimator of `f` (Definition 3 with
`X = {0,1}ⁿ`) on the whole cube: `h(x) ≤ g(x)` for all `x ∈ Cₙ = [0,1]ⁿ`. -/
theorem g_ge_underestimator {n : ℕ} (f : (Fin n → ℝ) → ℝ) (h : (Fin n → ℝ) → ℝ)
    (hh : IsConvexUnderestimator (binaryPoints n) f h) :
    ∀ x ∈ cube n, h x ≤ g f x := by sorry

end SDDiP.Envelope
