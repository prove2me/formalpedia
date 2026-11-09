-- Prove2me | Theorems.Thm_SublinearPauli_Fidelity_lab_state_norm
-- name    : SublinearPauli.Fidelity.lab_state_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:47:27.968776+00:00
-- url     : https://prove2.me/theorems/db4590e9-b488-475b-a63a-7bd237dc4c9f
-- title:
--   Lemma 4 — lab state norm, $\max_\sigma W_\gamma(\sigma)\le 2^{N(1-2\gamma)/(1-\gamma)}$
-- statement:
--   Let $0\le\gamma<1$. For every $N$-qubit density matrix $\sigma$,
--   $$W_\gamma(\sigma)\le2^{N\left(\frac{1-2\gamma}{1-\gamma}\right)},$$
--   so $\max_{\sigma\in D(\mathbb C^d)}W_\gamma(\sigma)$ is at most the right-hand side. For $\gamma>\tfrac12$ the exponent is negative.
--
--   Here $W_\gamma(\sigma)=\sum_{(Q,Q')\in\mathcal S}|\hat\sigma(Q\Delta Q')|^{2/(1-\gamma)}/3^{N-w(Q\cap Q')}$. This is the third ingredient of Theorem 2; at $\gamma=0$ it is attained by Pauli eigenstates.
--
--   The maximum over density matrices is attained.
--
--   Differences from the source:
--   - encoding: a maximum over density matrices → an existential real value that is the greatest element of the energy-value set and satisfies the printed bound; reason: `IsGreatest` expresses both attainment and domination.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, p.15, Lemma 4 (proof pp.15–16)

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Energies

open ClassicalShadow.Linear

namespace SublinearPauli.Fidelity

/-- **Lemma 4** (Lab state norm), p.15. For every `0 ≤ γ < 1` and every `N`-qubit density matrix
`σ`, `W_γ(σ) ≤ 2^{N (1 − 2γ)/(1 − γ)}`; the maximum over all density matrices is attained and is at most the right-hand side. -/
theorem lab_state_norm {N : ℕ} (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ m : ℝ,
      IsGreatest {v : ℝ | ∃ σ : Op N, WildeQIT.IsDensityOperator σ ∧ v = energyW γ σ} m ∧
        m ≤ (2 : ℝ) ^ ((N : ℝ) * ((1 - 2 * γ) / (1 - γ))) := by sorry

end SublinearPauli.Fidelity
