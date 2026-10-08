-- Prove2me | Theorems.Thm_RadGauss_LipschitzGaussian_cubeExtension_spec
-- name    : RadGauss.LipschitzGaussian.cubeExtension_spec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:06:15.787184+00:00
-- url     : https://prove2.me/theorems/b02478c5-a72d-4c73-850f-2e6d9768c8a2
-- title:
--   Proof of Theorem 16 — the extension of g to ℝ^k is well defined, extends g, maps into [−1,1], has g(0)=0 and is 1-Lipschitz
-- statement:
--   Let $k \ge 1$ and let $g : \{\pm1\}^k \to \{\pm1\}$ be a boolean function. Extend $g$ to $\mathbb R^k$ by $g(x) = (1 - \|x - a\|)g(a)$ if $\|x - a\| < 1$ for some $a \in \{\pm1\}^k$, and $g(x) = 0$ otherwise ($\|\cdot\|$ the Euclidean norm). Then:
--
--   1. the extension is well defined: at most one vertex $a$ of the cube satisfies $\|x - a\| < 1$, for any $x \in \mathbb R^k$;
--   2. it agrees with $g$ on the cube: $g(a)$ is unchanged for $a \in \{\pm1\}^k$;
--   3. it maps $\mathbb R^k$ into $[-1, 1]$;
--   4. $g(0) = 0$;
--   5. it is Lipschitz with constant $1$:
--   $$
--   |g(x) - g(x')| \le \|x - x'\| \qquad (x, x' \in \mathbb R^k).
--   $$
--
--   These are exactly the properties that let Theorem 14 be applied with $m = k$ and $\phi = g$ to obtain Theorem 16.
--
--   **Formalization Note** The page tacitly has $k \ge 1$; for $k = 0$ the cube is the single point $0$, so $g(0) = g(\text{the empty sign vector}) = \pm 1 \ne 0$. The hypothesis $0 < k$ is therefore added.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 472 (PDF p. 10), proof of Theorem 16

import Mathlib
import Definitions.Def_RadGauss_LipschitzGaussian_cubeExtension

namespace RadGauss.LipschitzGaussian

/-- **Proof of Theorem 16** (p. 472): the extension `g : ℝ^k → [−1, 1]` of a boolean function
`g : {±1}^k → {±1}` is well defined (at most one cube vertex lies within distance `< 1` of any
point), agrees with `g` on the cube, takes values in `[−1, 1]`, satisfies `g(0) = 0`, and is
Lipschitz with constant `1` for the Euclidean distance. Here `k ≥ 1`. -/
theorem cubeExtension_spec {k : ℕ} (hk : 0 < k) (g : (Fin k → ℤˣ) → ℤˣ) :
    (∀ (x : EuclideanSpace ℝ (Fin k)) (a b : Fin k → ℤˣ),
        ‖x - cubeVertex a‖ < 1 → ‖x - cubeVertex b‖ < 1 → a = b) ∧
      (∀ a, cubeExtension g (cubeVertex a) = ((g a : ℤ) : ℝ)) ∧
      (∀ x, cubeExtension g x ∈ Set.Icc (-1 : ℝ) 1) ∧
      cubeExtension g 0 = 0 ∧
      LipschitzWith 1 (cubeExtension g) := by sorry

end RadGauss.LipschitzGaussian
