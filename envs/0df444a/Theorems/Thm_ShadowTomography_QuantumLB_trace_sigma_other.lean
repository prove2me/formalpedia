-- Prove2me | Theorems.Thm_ShadowTomography_QuantumLB_trace_sigma_other
-- name    : ShadowTomography.QuantumLB.trace_sigma_other
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:38:07.105984+00:00
-- url     : https://prove2.me/theorems/bb103639-bae9-44e9-adfc-3b0278291fdb
-- title:
--   Proof of Theorem 19, p. 23 — $|\operatorname{Tr}(\mathbb P_j\sigma_i)-1/2| = 6\varepsilon|\operatorname{Tr}(\mathbb P_j\rho_i)-1/2|\le\varepsilon/2$
-- statement:
--   Let $N\ge1$ and let $\mathbb P_1,\dots,\mathbb P_K$ be orthogonal projections onto $N/2$-dimensional subspaces of $\mathbb C^N$ satisfying Eq. (2): with $\rho_j=\tfrac2N\mathbb P_j$,
--
--   $$
--   \Bigl|\operatorname{Tr}(\mathbb P_i\rho_j)-\frac12\Bigr|\le\frac1{12}\qquad (i\ne j).
--   $$
--
--   Let $\varepsilon\ge0$ and $\sigma_i := (1-6\varepsilon)\,\mathbb I/N + 6\varepsilon\rho_i$. Then for all $i\neq j$,
--
--   $$
--   \Bigl|\operatorname{Tr}(\mathbb P_j\sigma_i)-\frac12\Bigr| = 6\varepsilon\,\Bigl|\operatorname{Tr}(\mathbb P_j\rho_i)-\frac12\Bigr| \le \frac{\varepsilon}{2}.
--   $$
--
--   Together with $\operatorname{Tr}(\mathbb P_i\sigma_i)=\tfrac12+3\varepsilon$, this shows that estimating every $\operatorname{Tr}(\mathbb P_j\sigma_i)$ to within $\pm\varepsilon$ identifies $i$.
--
--   **Formalization Note** The hypothesis $\varepsilon\ge0$ (the paper's $\varepsilon$ is positive) is what lets $6\varepsilon$ come out of the absolute value.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 23, proof of Theorem 19, display for |Tr(ℙ_jσ_i) − 1/2|

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_IsHalfProjector
import Definitions.Def_ShadowTomography_QuantumLB_rhoState
import Definitions.Def_ShadowTomography_QuantumLB_sigmaState

namespace ShadowTomography.QuantumLB

/-- Proof of Theorem 19, p. 23: under Eq. (2), for `i ≠ j`,
`|Tr(ℙ_j σ_i) − 1/2| = 6ε |Tr(ℙ_j ρ_i) − 1/2| ≤ ε/2`. -/
theorem trace_sigma_other {N K : ℕ} (hN : 1 ≤ N) (P : Fin K → Matrix (Fin N) (Fin N) ℂ)
    (hP : ∀ i, IsHalfProjector (P i))
    (h2 : ∀ i j, i ≠ j → |(P i * rhoState (P j)).trace.re - 1 / 2| ≤ 1 / 12)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ i j, i ≠ j →
      |(P j * sigmaState (P i) ε).trace.re - 1 / 2|
          = 6 * ε * |(P j * rhoState (P i)).trace.re - 1 / 2| ∧
        |(P j * sigmaState (P i) ε).trace.re - 1 / 2| ≤ ε / 2 := by sorry

end ShadowTomography.QuantumLB
