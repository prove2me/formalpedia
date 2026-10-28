-- Prove2me | Theorems.Thm_ShadowTomography_QuantumLB_mutual_information
-- name    : ShadowTomography.QuantumLB.mutual_information
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:38:44.268592+00:00
-- url     : https://prove2.me/theorems/813bd260-4b0e-4766-834f-7a77f09e0a6f
-- title:
--   Proof of Theorem 19, p. 24 — $I(\zeta;i)\le T(\log_2 N - S(\sigma_i))$
-- statement:
--   Let $K\ge1$, and let $\sigma_1,\dots,\sigma_K$ be mixed states on $\mathbb C^N$ that all have the same von Neumann entropy $S(\sigma_i)=s$. Let $T\in\mathbb N$, let $i$ be uniform on $[K]$, and let $\zeta := \mathbb E_{i\in[K]}[\sigma_i^{\otimes T}]$. Then the quantum mutual information between $\zeta$ and the classical index $i$ satisfies
--
--   $$
--   I(\zeta; i) = S(\zeta) - S(\zeta\mid i) \le T\bigl(\log_2 N - s\bigr).
--   $$
--
--   The paper's justification is that $\zeta$ is an $N^T$-dimensional state, so $S(\zeta)\le T\log_2 N$, while $S(\sigma_i^{\otimes T}) = T\,S(\sigma_i)$. Combined with the entropy bound for $\sigma_i$, it shows that $T$ copies carry only $O(T\varepsilon^2)$ bits about $i$.
--
--   **Formalization Note** The printed second line $S(\zeta)-S(\sigma_i^{\otimes T})$ has a free index $i$; it is meaningful because all $\sigma_i$ have the same spectrum. The hypothesis "all $S(\sigma_i)$ equal $s$" expresses this. $I(\zeta;i)$ is the definition `holevoInfo`, with $S(\zeta\mid i)$ the average of $S(\sigma_i^{\otimes T})$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 24, proof of Theorem 19, display for I(ζ; i)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_ShadowTomography_QuantumLB_holevoInfo

namespace ShadowTomography.QuantumLB

/-- Proof of Theorem 19, p. 24, mutual-information display: if `σ_1, …, σ_K` are mixed
states on `ℂ^N` with a common entropy `s`, then `I(ζ; i) ≤ T (log₂ N − s)`. -/
theorem mutual_information {N K : ℕ} (hK : 1 ≤ K) (σ : Fin K → Matrix (Fin N) (Fin N) ℂ)
    (hσ : ∀ i, WildeQIT.IsDensityOperator (σ i)) (s : ℝ) (hs : ∀ i, vnEntropy (σ i) = s)
    (T : ℕ) :
    holevoInfo σ T ≤ (T : ℝ) * (Real.logb 2 N - s) := by sorry

end ShadowTomography.QuantumLB
