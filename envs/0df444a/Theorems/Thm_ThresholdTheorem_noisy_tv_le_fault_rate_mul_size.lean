-- Prove2me | Theorems.Thm_ThresholdTheorem_noisy_tv_le_fault_rate_mul_size
-- name    : ThresholdTheorem.noisy_tv_le_fault_rate_mul_size
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T00:58:40.297056+00:00
-- url     : https://prove2.me/theorems/5ae33ce4-3f6e-4f9f-b697-69d8ac239bf0
-- title:
--   Unencoded circuits: output error at most $p\,|C|$
-- statement:
--   **Errors accumulate at most linearly (unencoded circuits).** Let $C$ be any circuit on a finite register and let $0\le p\le 1$. For every independent stochastic noise model with fault rate at most $p$,
--
--   $$d_{\mathrm{TV}}\big(P_{\mathrm{noisy}}(C),\,P_{\mathrm{ideal}}(C)\big)\;\le\;p\,|C| ,$$
--
--   where $P_{\mathrm{noisy}}(C)$ and $P_{\mathrm{ideal}}(C)$ are the outcome distributions of measuring all qubits after the noisy and the noiseless runs of $C$, and $|C|$ is the number of locations of $C$.
--
--   Without error correction, a circuit with $p(n)$ components is only reliable when $p\cdot p(n)$ is small; this is the baseline that fault tolerance improves on, and the same bound is the level-$0$ case of the concatenated construction.
-- source:
--   Wikipedia, "Threshold theorem" (revision oldid=1360742213, https://en.wikipedia.org/w/index.php?title=Threshold_theorem&oldid=1360742213), section "Explanation"; the boxed statement is quoted there from M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, 10th anniversary ed., Cambridge University Press, p. 481.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model

open ThresholdTheorem

namespace ThresholdTheorem
theorem noisy_tv_le_fault_rate_mul_size {Q : Type*} [Fintype Q] [DecidableEq Q]
    (C : Circuit Q) (p : ℝ) (hp : p ≤ 1) (N : NoiseModel p) :
    tvDist (outDist (noisyState N C)) (outDist (idealState C)) ≤ p * C.size := by sorry
end ThresholdTheorem
