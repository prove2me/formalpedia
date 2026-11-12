-- Prove2me | Theorems.Thm_TestableSanitization_Robust_theorem_1_log2
-- name    : TestableSanitization.Robust.theorem_1_log2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:18:41.794683+00:00
-- url     : https://prove2.me/theorems/497238d3-123e-4e58-965f-e71dc1538cb6
-- title:
--   Theorem 1 with runtime $\tilde O(dq+d^2\log(2+\mu/r))$ (corrected: the bound its proof establishes)
-- statement:
--   **Source** (Theorem 1, p. 9): for every $d \ge 1$, $\alpha > 1$, $\eta, \zeta \in (0, 1/2)$ and $\mu > 0$ there is an $(\alpha, \eta, \eta)$-testable sanitization algorithm with success probability $1 - \zeta$ for all $D$ with $\mathbb{E}\|x\| \le \mu$, with $O(\log(1/\zeta)/\eta)$ samples, $O(m \log(m/\zeta)(1 + 1/(\alpha^2 - 1))^d)$ queries and runtime $\tilde O(dq + d^2 \log(1 + \mu/r))$.
--
--   **Variant:** the same statement (same machine, same Definition 2 with one universal completeness constant, same explicit constants $C, k$ for $O$ and $\tilde O$), with the runtime bound
--   $$C\big(d q_0 + d^2 \log(2 + \mu/r)\big) \log(2 + d + 1/\eta + 1/\zeta)^k + C.$$
--
--   **Difference:** $\log(1 + \mu/r)$ is replaced by $\log(2 + \mu/r)$, which is what the proof on p. 27 concludes; the bound of the variant is never smaller than the printed one and differs materially when $\mu/r$ is small, where the printed bound drops below the $\Omega(d^2)$ cost of storing the $T$ perturbation vectors.
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 9 (PDF 11), Theorem 1; p. 27 (PDF 29), proof (corrected runtime)

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Boundary
import Definitions.Def_TestableSanitization_Robust_Sanitizer
open MeasureTheory

namespace TestableSanitization.Robust

theorem theorem_1_log2 :
    ∃ (C : ℝ) (k : ℕ) (c : ℝ), 0 < C ∧ 0 < c ∧ c < 1 ∧
      ∀ (d : ℕ) (α η ζ μ : ℝ), 1 ≤ d → 1 < α → 0 < η → η < 1 / 2 → 0 < ζ → ζ < 1 / 2 → 0 < μ →
        ∃ P E : Program, Admissible P ∧ Admissible E ∧ Deterministic E ∧
          IsTestableSanitizer d α η η ζ c μ P E ∧
          CostBounded d α η ζ μ
            (fun _ => C * (Real.log (1 / ζ) / η) + C)
            (fun _ => C * ((Real.log (1 / ζ) / η) * Real.log ((Real.log (1 / ζ) / η) / ζ) *
                (1 + 1 / (α ^ 2 - 1)) ^ d) + C)
            (fun r => C * ((d : ℝ) * ((Real.log (1 / ζ) / η) *
                Real.log ((Real.log (1 / ζ) / η) / ζ) * (1 + 1 / (α ^ 2 - 1)) ^ d) +
                (d : ℝ) ^ 2 * Real.log (2 + μ / r)) *
                Real.log (2 + d + 1 / η + 1 / ζ) ^ k + C)
            P := by sorry

end TestableSanitization.Robust
