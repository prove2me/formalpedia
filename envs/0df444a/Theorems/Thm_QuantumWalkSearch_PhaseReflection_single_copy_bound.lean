-- Prove2me | Theorems.Thm_QuantumWalkSearch_PhaseReflection_single_copy_bound
-- name    : QuantumWalkSearch.PhaseReflection.single_copy_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T08:46:42.260967+00:00
-- url     : https://prove2.me/theorems/c36ee784-b7f2-40f9-9229-60dd5b11e5a4
-- title:
--   Proof of Theorem 6 — with $s=\lceil\log_2(2\pi/\Delta)\rceil$, every phase $\theta\in[\Delta/2,\pi-\Delta/2]$ has $|\langle0^s|\omega\rangle|\le1/2$
-- statement:
--   Let $0<\Delta\le\pi$ and $s=\lceil\log_2(2\pi/\Delta)\rceil$. For every $\theta$ with $\Delta/2\le\theta\le\pi-\Delta/2$,
--   $$\frac{|\sin(2^s\theta)|}{2^s\sin\theta}\ \le\ \frac12 .$$
--
--   By Theorem 5, the left side is the amplitude on $|0^s\rangle$ after phase estimation of an eigenvector with eigenvalue $e^{2i\theta}$. The range of $\theta$ covers the eigenvalues $e^{2i\theta}$ and $e^{-2i\theta}=e^{2i(\pi-\theta)}$ with $\Delta(P)/2\le\theta<\pi/2$ and also the eigenvalue $-1$ ($\theta=\pi/2$), which are the eigenvalues of $W(P)$ on the part of $\mathcal A+\mathcal B$ orthogonal to $|\pi\rangle$. This is the single-copy step of the proof of Theorem 6.
--
--   **Formalization Note** The paper's sentence lists only $\Delta(P)/2\le\theta<\pi/2$ and the phases $e^{\pm2i\theta}$; the eigenvalue $-1$, which Theorem 4 part 3 allows on $\mathcal A+\mathcal B$, is included here. $\lceil\cdot\rceil$ is `Nat.ceil`, $\log_2$ is `Real.logb 2`.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, pp. 9–10, proof of Theorem 6 (unnumbered: "By definition of s, the state |ω⟩ holding the estimate for any phase θ ≠ 0 then satisfies |⟨0^s|ω⟩| ≤ 1/2")

import Mathlib
import Definitions.Def_QuantumWalkSearch_PhaseReflection_ReflectionCircuit

namespace QuantumWalkSearch.PhaseReflection

/-- Proof of Theorem 6, pp. 9–10: with `s = ⌈log₂(2π/Δ)⌉`, every phase `θ` with
`Δ/2 ≤ θ ≤ π − Δ/2` has phase-estimation amplitude `|sin(2^s θ)| / (2^s sin θ) ≤ 1/2` on `|0^s⟩`. -/
theorem single_copy_bound (Δ θ : ℝ) (hΔ : 0 < Δ) (hΔπ : Δ ≤ Real.pi) (hθ₁ : Δ / 2 ≤ θ)
    (hθ₂ : θ ≤ Real.pi - Δ / 2) :
    |Real.sin (2 ^ precision Δ * θ)| / (2 ^ precision Δ * Real.sin θ) ≤ 1 / 2 := by sorry

end QuantumWalkSearch.PhaseReflection
