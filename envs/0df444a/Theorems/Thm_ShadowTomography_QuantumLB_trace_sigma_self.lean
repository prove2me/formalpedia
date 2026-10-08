-- Prove2me | Theorems.Thm_ShadowTomography_QuantumLB_trace_sigma_self
-- name    : ShadowTomography.QuantumLB.trace_sigma_self
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:34:30.528585+00:00
-- url     : https://prove2.me/theorems/8ff53c6a-8efb-4384-85b7-4e95b34e4ad9
-- title:
--   Proof of Theorem 19, p. 23 — $\operatorname{Tr}(\mathbb P_i\sigma_i) = 1/2 + 3\varepsilon$
-- statement:
--   Let $N\ge 1$, let $\mathbb P$ be the orthogonal projection onto an $N/2$-dimensional subspace of $\mathbb C^N$, let $\varepsilon\in\mathbb R$, and let
--
--   $$
--   \sigma := (1-6\varepsilon)\frac{\mathbb I}{N} + 6\varepsilon\cdot\frac2N\mathbb P .
--   $$
--
--   Then the measurement $\mathbb P$ accepts $\sigma$ with probability
--
--   $$
--   \operatorname{Tr}(\mathbb P\sigma) = \frac12 + 3\varepsilon .
--   $$
--
--   So the designated measurement $\mathbb P_i$ is biased by $3\varepsilon$ towards accepting its own hard state $\sigma_i$.
--
--   **Formalization Note** No sign condition on $\varepsilon$ is needed. The hypothesis $N\ge1$ excludes the empty matrix, whose trace is $0$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 23, proof of Theorem 19, display for Tr(ℙ_iσ_i)

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_IsHalfProjector
import Definitions.Def_ShadowTomography_QuantumLB_sigmaState

namespace ShadowTomography.QuantumLB

/-- Proof of Theorem 19, p. 23: `Tr(ℙ σ) = 1/2 + 3ε` for `σ = (1 − 6ε) 𝕀/N + 6ε (2/N) ℙ`. -/
theorem trace_sigma_self {N : ℕ} (hN : 1 ≤ N) (P : Matrix (Fin N) (Fin N) ℂ)
    (hP : IsHalfProjector P) (ε : ℝ) :
    (P * sigmaState P ε).trace.re = 1 / 2 + 3 * ε := by sorry

end ShadowTomography.QuantumLB
