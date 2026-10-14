-- Prove2me | Theorems.Thm_ThresholdTheorem_level_one_error_suppression
-- name    : ThresholdTheorem.level_one_error_suppression
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:59:37.872325+00:00
-- url     : https://prove2.me/theorems/461e312a-3410-4e3c-b930-144609d2651c
-- title:
--   Better gates: one level of encoding gives error $O(p^2)$ per location
-- statement:
--   **Better gates from error-correcting codes (one level of encoding).** There are constants $c>0$ and $A$, a block size $b$ and a decoder $\mathrm{dec}:\{0,1\}^b\to\{0,1\}$ such that every ideal circuit $C$ on $n$ qubits has a physical simulation $C'$ on $n$ blocks of $b$ qubits with $|C'|\le A\,|C|$ and, for every $0\le p$ with $cp<1$ and every independent stochastic noise model with fault rate at most $p$,
--
--   $$d_{\mathrm{TV}}\big(\mathrm{dec}_*P_{\mathrm{noisy}}(C'),\,P_{\mathrm{ideal}}(C)\big)\;\le\;c\,p^{2}\,|C| .$$
--
--   Compared with the unencoded bound $p\,|C|$, each simulated location now fails with probability $O(p^2)$ instead of $O(p)$: the encoded gates are larger, but because of error correction they fail less often than the original gates once $p$ is small.
-- source:
--   Wikipedia, "Threshold theorem" (revision oldid=1360742213, https://en.wikipedia.org/w/index.php?title=Threshold_theorem&oldid=1360742213), section "Explanation"; the boxed statement is quoted there from M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, 10th anniversary ed., Cambridge University Press, p. 481.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model

open ThresholdTheorem

namespace ThresholdTheorem
theorem level_one_error_suppression :
    ∃ (c A : ℝ) (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2), 0 < c ∧
      ∀ (n : ℕ) (C : Circuit (Fin n)), ∃ C' : Circuit (Fin n × Fin b),
        (C'.size : ℝ) ≤ A * C.size ∧
        ∀ (p : ℝ), 0 ≤ p → c * p < 1 → ∀ N : NoiseModel p,
          tvDist (decodeDist dec (outDist (noisyState N C'))) (outDist (idealState C))
            ≤ c * p ^ 2 * C.size := by sorry
end ThresholdTheorem
