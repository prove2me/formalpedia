-- Prove2me | Theorems.Thm_SublinearPauli_Fidelity_pauli_graph_edge_weight
-- name    : SublinearPauli.Fidelity.pauli_graph_edge_weight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:47:20.035546+00:00
-- url     : https://prove2.me/theorems/c0f49bb3-25fb-4698-90bc-6a62675e6c4d
-- title:
--   Theorem 3 — edge weight of the random Pauli graph, $\max_\rho E_\gamma(\rho)\le(4/3)^N4^{N(\lambda\gamma-1)/((1+\lambda)(1+\gamma))}$
-- statement:
--   Let $\lambda=\frac{1+\sqrt{33}}8$ and $\gamma\in[0,\lambda]$. For every $N$-qubit density matrix $\rho$,
--   $$E_\gamma(\rho)\le\Bigl(\frac43\Bigr)^N\cdot4^{N\left(\frac{\lambda\gamma-1}{(1+\lambda)(1+\gamma)}\right)},$$
--   so $\max_{\rho\in D(\mathbb C^d)}E_\gamma(\rho)$ is at most the right-hand side.
--
--   Here $E_\gamma(\rho)=\sum_{(Q,Q')\in\mathcal S}|\hat\rho(Q)|^{2/(1+\gamma)}|\hat\rho(Q')|^{2/(1+\gamma)}/3^{N-w(Q\cap Q')}$ is the expected edge weight of the random Pauli graph. This is the second ingredient of Theorem 2, used there at $\gamma=\lambda$.
--
--   The maximum over density matrices is attained.
--
--   Differences from the source:
--   - encoding: a maximum over density matrices → an existential real value that is the greatest element of the energy-value set and satisfies the printed bound; reason: `IsGreatest` expresses both attainment and domination.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, p.13, Theorem 3 (proof pp.13–15)

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Energies

open ClassicalShadow.Linear

namespace SublinearPauli.Fidelity

/-- **Theorem 3** (Edge weight of random Pauli graph), p.13. With `λ = (1 + √33)/8`, for every
`γ ∈ [0, λ]` and every `N`-qubit density matrix `ρ`,
`E_γ(ρ) ≤ (4/3)^N · 4^{N (λγ − 1)/((1+λ)(1+γ))}`; the maximum over all density matrices is attained and is at most the
right-hand side. -/
theorem pauli_graph_edge_weight {N : ℕ} (γ : ℝ) (hγ0 : 0 ≤ γ) (hγlam : γ ≤ lam) :
    ∃ m : ℝ,
      IsGreatest {v : ℝ | ∃ ρ : Op N, WildeQIT.IsDensityOperator ρ ∧ v = energyE γ ρ} m ∧
        m ≤ (4 / 3 : ℝ) ^ N * (4 : ℝ) ^ ((N : ℝ) * ((lam * γ - 1) / ((1 + lam) * (1 + γ)))) := by sorry

end SublinearPauli.Fidelity
