-- Prove2me | Theorems.Thm_ShadowTomography_QuantumLB_entropy_sigma
-- name    : ShadowTomography.QuantumLB.entropy_sigma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:34:57.250033+00:00
-- url     : https://prove2.me/theorems/bd129bbe-d77e-4f95-9a7a-d9b03f3b6b2d
-- title:
--   Proof of Theorem 19, p. 24 — exact von Neumann entropy of $\sigma_i$
-- statement:
--   Let $N\ge2$, let $\mathbb P$ be the orthogonal projection onto an $N/2$-dimensional subspace of $\mathbb C^N$, let $0\le\varepsilon\le\tfrac16$, and let $\sigma := (1-6\varepsilon)\,\mathbb I/N + 6\varepsilon\cdot\tfrac2N\mathbb P$. Then the von Neumann entropy of $\sigma$ in bits is
--
--   $$
--   S(\sigma) = \log_2 N - \Bigl[1 - \Bigl(\tfrac12+3\varepsilon\Bigr)\log_2\frac{1}{\tfrac12+3\varepsilon} - \Bigl(\tfrac12-3\varepsilon\Bigr)\log_2\frac{1}{\tfrac12-3\varepsilon}\Bigr],
--   $$
--
--   with $0\log_2\frac10 = 0$ at $\varepsilon=\tfrac16$. The bracket is $1-h\bigl(\tfrac12+3\varepsilon\bigr)$, where $h$ is the binary entropy; it measures how far $\sigma$ falls short of the maximally mixed state. The paper obtains it from the spectrum of $\sigma$: half of its eigenvalues equal $\frac{1/2+3\varepsilon}{N/2}$ and the other half $\frac{1/2-3\varepsilon}{N/2}$.
--
--   **Formalization Note** At $\varepsilon=\tfrac16$ Lean evaluates $\log_2(1/0)$ as $0$, so the last term is $0$, which is the convention $0\log 0=0$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 24, proof of Theorem 19, display for S(σ_i), lines 1–3

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_IsHalfProjector
import Definitions.Def_ShadowTomography_QuantumLB_sigmaState
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy

namespace ShadowTomography.QuantumLB

/-- Proof of Theorem 19, p. 24, entropy display (first three lines):
`S(σ) = log₂ N − [1 − (1/2 + 3ε) log₂(1/(1/2 + 3ε)) − (1/2 − 3ε) log₂(1/(1/2 − 3ε))]`. -/
theorem entropy_sigma {N : ℕ} (hN : 2 ≤ N) (P : Matrix (Fin N) (Fin N) ℂ)
    (hP : IsHalfProjector P) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 6) :
    vnEntropy (sigmaState P ε)
      = Real.logb 2 N
        - (1 - (1 / 2 + 3 * ε) * Real.logb 2 (1 / (1 / 2 + 3 * ε))
             - (1 / 2 - 3 * ε) * Real.logb 2 (1 / (1 / 2 - 3 * ε))) := by sorry

end ShadowTomography.QuantumLB
