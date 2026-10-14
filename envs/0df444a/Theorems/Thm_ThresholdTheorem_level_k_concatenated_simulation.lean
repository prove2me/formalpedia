-- Prove2me | Theorems.Thm_ThresholdTheorem_level_k_concatenated_simulation
-- name    : ThresholdTheorem.level_k_concatenated_simulation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T01:02:17.435511+00:00
-- url     : https://prove2.me/theorems/6d175c37-2a54-43c5-89c0-14cf15f2cfd5
-- title:
--   Level-$k$ concatenated simulation: error $(cp)^{2^k}/c$ per location, size $O(d^k)$
-- statement:
--   **Concatenated simulation at every level.** There are constants $c>0$, $A$ and $d\in\mathbb N$ such that for every number of levels $k$ there are a block size $b$ and a decoder $\mathrm{dec}:\{0,1\}^b\to\{0,1\}$ with the following property: every ideal circuit $C$ on $n$ qubits has a physical simulation $C'$ on $n$ blocks of $b$ qubits with
--
--   $$|C'|\;\le\;A\,d^{k}\,|C|,$$
--
--   and for every $0\le p$ with $cp<1$ and every independent stochastic noise model with fault rate at most $p$,
--
--   $$d_{\mathrm{TV}}\big(\mathrm{dec}_*P_{\mathrm{noisy}}(C'),\,P_{\mathrm{ideal}}(C)\big)\;\le\;\frac{(c\,p)^{2^{k}}}{c}\,|C| .$$
--
--   This is the statement that better gates can be used recursively to build even better gates: after $k$ levels each location fails with probability at most $(cp)^{2^k}/c$, at a cost of a factor $d^k$ in size. For $k=0$ it is the unencoded bound, and $k=1$ is the one-level statement.
-- source:
--   Wikipedia, "Threshold theorem" (revision oldid=1360742213, https://en.wikipedia.org/w/index.php?title=Threshold_theorem&oldid=1360742213), section "Explanation"; the boxed statement is quoted there from M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, 10th anniversary ed., Cambridge University Press, p. 481.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model

open ThresholdTheorem

namespace ThresholdTheorem
theorem level_k_concatenated_simulation :
    ∃ (c A : ℝ) (d : ℕ), 0 < c ∧ ∀ k : ℕ, ∃ (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
      ∀ (n : ℕ) (C : Circuit (Fin n)), ∃ C' : Circuit (Fin n × Fin b),
        (C'.size : ℝ) ≤ A * (d : ℝ) ^ k * C.size ∧
        ∀ (p : ℝ), 0 ≤ p → c * p < 1 → ∀ N : NoiseModel p,
          tvDist (decodeDist dec (outDist (noisyState N C'))) (outDist (idealState C))
            ≤ (c * p) ^ (2 ^ k) / c * C.size := by sorry
end ThresholdTheorem
