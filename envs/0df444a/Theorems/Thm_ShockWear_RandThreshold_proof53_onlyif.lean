-- Prove2me | Theorems.Thm_ShockWear_RandThreshold_proof53_onlyif
-- name    : ShockWear.RandThreshold.proof53_onlyif
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:53:45.413986+00:00
-- url     : https://prove2.me/theorems/df22bbf5-87bd-4545-aa33-760c77c6ea37
-- title:
--   Proof of Theorem 5.3, p. 645 — submultiplicativity for every damage law gives Ḡ(s + j s/k) ≤ Ḡ(s)Ḡ(j s/k)
-- statement:
--   Let $G$ be a distribution with $G(z) = 0$ for $z < 0$ and survival function $\bar G = 1 - G$. For a distribution $F$ with $F(z) = 0$ for $z < 0$ put $\bar P_k(F) = \int_0^\infty F^{(k)}(x)\, dG(x)$, $k = 0, 1, \dots$. Suppose that for **every** such $F$,
--   $$\bar P_{j+k}(F) \le \bar P_j(F)\,\bar P_k(F), \qquad j, k = 0, 1, \dots .$$
--   Then for every $s > 0$ and every $k = 1, 2, \dots$, with $x_k = s/k$,
--   $$\bar G(s + j x_k) \le \bar G(s)\,\bar G(j x_k), \qquad j = 0, 1, \dots .$$
--
--   This is the intermediate inequality of the "only if" half of Theorem 5.3; letting $k \to \infty$ with $j x_k$ close to a given $t$ yields the NBU property of $G$.
--
--   **Formalization Note.** $\bar P_k$ is (5.1) as printed. The paper obtains the display by taking $F$ degenerate at $x_k$ and reading $\bar P_m$ as $\bar G(m x_k)$, which is the paper's $E\bar G$ form under its no-common-discontinuities convention. With (5.1) as printed, $F$ degenerate at $x_k$ gives $\bar P_m = P\{Y \ge m x_k\} = \bar G(m x_k -)$, the left limit; the display with $\bar G$ itself still follows from the hypothesis (for example by letting the atom of $F$ decrease to $x_k$ and using right continuity of $\bar G$, with a separate argument at $j = 0$), but not in literally one step from (5.1). The statement is the paper's display; only the route differs.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 645, proof of Theorem 5.3, second display

import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model

namespace ShockWear.RandThreshold

open MeasureTheory ProbabilityTheory

theorem proof53_onlyif (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hsub : ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Set.Iio 0) = 0 →
      ∀ j k : ℕ, randP μ ν (j + k) ≤ randP μ ν j * randP μ ν k) :
    ∀ s : ℝ, 0 < s → ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ,
      survOf ν (s + j * (s / k)) ≤ survOf ν s * survOf ν (j * (s / k)) := by sorry

end ShockWear.RandThreshold
