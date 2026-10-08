-- Prove2me | Theorems.Thm_ShadowTomography_QuantumLB_entropy_sigma_lower
-- name    : ShadowTomography.QuantumLB.entropy_sigma_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:35:04.911486+00:00
-- url     : https://prove2.me/theorems/98e277f7-f16f-40c4-9dd5-531beecc9c53
-- title:
--   Proof of Theorem 19, p. 24 — $S(\sigma_i)\ge\log_2 N - O(\varepsilon^2)$
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $N\ge2$, let $\mathbb P$ be the orthogonal projection onto an $N/2$-dimensional subspace of $\mathbb C^N$, let $0\le\varepsilon\le\tfrac16$, and let $\sigma := (1-6\varepsilon)\,\mathbb I/N + 6\varepsilon\cdot\tfrac2N\mathbb P$. Then
--
--   $$
--   S(\sigma) \ge \log_2 N - C\varepsilon^2 ,
--   $$
--
--   where $S$ is the von Neumann entropy in bits. Thus each hard state is within $O(\varepsilon^2)$ bits of maximal entropy, which is what limits the information that each copy carries about the index $i$.
--
--   **Formalization Note** The $O(\varepsilon^2)$ is a single constant $C$, quantified before $N$, $\mathbb P$ and $\varepsilon$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 24, proof of Theorem 19, display for S(σ_i), line 4

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_IsHalfProjector
import Definitions.Def_ShadowTomography_QuantumLB_sigmaState
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy

namespace ShadowTomography.QuantumLB

/-- Proof of Theorem 19, p. 24, entropy display (last line): `S(σ) ≥ log₂ N − O(ε²)`,
with a universal constant `C`. -/
theorem entropy_sigma_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (P : Matrix (Fin N) (Fin N) ℂ) (ε : ℝ),
      2 ≤ N → IsHalfProjector P → 0 ≤ ε → ε ≤ 1 / 6 →
        Real.logb 2 N - C * ε ^ 2 ≤ vnEntropy (sigmaState P ε) := by sorry

end ShadowTomography.QuantumLB
