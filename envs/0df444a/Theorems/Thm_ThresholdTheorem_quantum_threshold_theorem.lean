-- Prove2me | Theorems.Thm_ThresholdTheorem_quantum_threshold_theorem
-- name    : ThresholdTheorem.quantum_threshold_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T01:04:37.888086+00:00
-- url     : https://prove2.me/theorems/b4c0161e-eb7b-4d33-a33f-e1ddddc3e0d7
-- title:
--   Threshold theorem for quantum computation
-- statement:
--   **Threshold theorem for quantum computation.** There are a threshold $p_{\mathrm{th}}>0$ and an exponent $c\in\mathbb N$ such that for every physical fault rate $0\le p<p_{\mathrm{th}}$ there is a constant $A$ with the following property.
--
--   For every number of logical qubits $n$, every depth $D$ and every target accuracy $0<\varepsilon<1$, there are a block size $b$ and a block decoder $\mathrm{dec}:\{0,1\}^b\to\{0,1\}$ such that every ideal circuit $C$ on $n$ qubits of depth $D$ can be simulated by a physical circuit $C'$ on $n$ blocks of $b$ qubits satisfying
--
--   $$|C'|\;\le\;A\,\Big(\log\tfrac{|C|}{\varepsilon}+1\Big)^{c}\,|C|$$
--
--   and, for **every** independent stochastic noise model with fault rate at most $p$,
--
--   $$d_{\mathrm{TV}}\Big(\mathrm{dec}_*\,P_{\mathrm{noisy}}(C'),\;P_{\mathrm{ideal}}(C)\Big)\;\le\;\varepsilon .$$
--
--   Here $|C|$ is the number of locations of $C$ (gates, preparations and idle steps), $P_{\mathrm{ideal}}(C)$ is the outcome distribution of measuring all qubits of the noiseless run of $C$, and $\mathrm{dec}_*P_{\mathrm{noisy}}(C')$ is the blockwise-decoded outcome distribution of the noisy run of $C'$.
--
--   This is the boxed statement of the source: a circuit with $p(n)$ gates can be simulated with error probability at most $\varepsilon$ using $O(\mathrm{poly}(\log(p(n)/\varepsilon))\,p(n))$ gates on hardware whose components fail with probability at most $p$, provided $p$ is below a constant threshold.
--
--   **Formalization Note** "Gates" of the source are counted as locations, idle steps included, as in the standard analyses where waiting qubits are also noisy. The source's $O(\log^c(p(n)/\varepsilon)\,p(n))$ is written non-asymptotically as $A(\log(|C|/\varepsilon)+1)^c|C|$. The block size and the decoder may depend on $n$, $D$, $\varepsilon$ and $p$ but not on the circuit $C$, which rules out decoders that encode the answer. The "reasonable assumptions about the noise" of the source are fixed as independent faults with arbitrary local fault channels.
-- source:
--   Wikipedia, "Threshold theorem" (revision oldid=1360742213, https://en.wikipedia.org/w/index.php?title=Threshold_theorem&oldid=1360742213), section "Explanation"; the boxed statement is quoted there from M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, 10th anniversary ed., Cambridge University Press, p. 481.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model

open ThresholdTheorem

namespace ThresholdTheorem
theorem quantum_threshold_theorem :
    ∃ pth : ℝ, 0 < pth ∧ ∃ c : ℕ, ∀ p : ℝ, 0 ≤ p → p < pth → ∃ A : ℝ,
      ∀ (n D : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
          ∀ C : Circuit (Fin n), C.length = D →
            ∃ C' : Circuit (Fin n × Fin b),
              (C'.size : ℝ) ≤ A * (Real.log (C.size / ε) + 1) ^ c * C.size ∧
              ∀ N : NoiseModel p,
                tvDist (decodeDist dec (outDist (noisyState N C'))) (outDist (idealState C))
                  ≤ ε := by sorry
end ThresholdTheorem
