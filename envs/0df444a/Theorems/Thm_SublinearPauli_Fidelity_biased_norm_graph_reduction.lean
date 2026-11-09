-- Prove2me | Theorems.Thm_SublinearPauli_Fidelity_biased_norm_graph_reduction
-- name    : SublinearPauli.Fidelity.biased_norm_graph_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:48:22.086739+00:00
-- url     : https://prove2.me/theorems/a76f3049-915b-43d8-b99e-6fb80c398fa8
-- title:
--   Lemma 2 — reducing the σ-biased Pauli norm to random Pauli graphs
-- statement:
--   Let $\rho$ and $\sigma$ be $N$-qubit density matrices, $d=2^N$, and let $0\le\gamma<1$. Then the $\sigma$-biased Pauli norm of $\rho$ satisfies
--   $$N_\sigma(\rho)\le\sqrt{\frac{E_\gamma(\rho)^{1+\gamma}\cdot W_\gamma(\sigma)^{1-\gamma}}{d}},$$
--   where $N_\sigma(\rho)=\sum_{B}\mathbb E_{x\sim\sigma,B}[s_\rho(B,x)^2]$ is the second moment of the shadow overlap statistic under Born's rule for $\sigma$, and $E_\gamma$, $W_\gamma$ are the graph energy and the lab-state norm.
--
--   The bound separates the target's contribution from the lab state's; it is the first of the three ingredients of Theorem 2.
--
--   Differences from the source:
--   - encoding: density matrices in $D(\mathbb C^d)$ and expectations under Born's rule → positive semidefinite trace-one complex matrices on bit strings, and the expectation as the finite sum of $\operatorname{Re}\operatorname{Tr}[\sigma M_x^B]\,s_\rho(B,x)^2$; reason: Lean convention, the same objects and values.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, p.13, Lemma 2 (N_σ(ρ) as in eq. (1), p.12)

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Measurement
import Definitions.Def_SublinearPauli_Fidelity_Energies

open ClassicalShadow.Linear

namespace SublinearPauli.Fidelity

/-- **Lemma 2** (Reducing the σ-biased Pauli norm to random Pauli graphs), p.13. For all
`N`-qubit density matrices `ρ, σ` and every `0 ≤ γ < 1`,
`N_σ(ρ) ≤ √(E_γ(ρ)^{1+γ} · W_γ(σ)^{1−γ} / d)`, `d = 2^N`. -/
theorem biased_norm_graph_reduction {N : ℕ} (ρ σ : Op N)
    (hρ : WildeQIT.IsDensityOperator ρ) (hσ : WildeQIT.IsDensityOperator σ)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    biasedNorm σ ρ ≤
      Real.sqrt (energyE γ ρ ^ (1 + γ) * energyW γ σ ^ (1 - γ) / (2 : ℝ) ^ N) := by sorry

end SublinearPauli.Fidelity
