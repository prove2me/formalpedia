-- Prove2me | Theorems.Thm_QuarticGauss390_EigenBound_lemma_3_2
-- name    : QuarticGauss390.EigenBound.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:44.573271+00:00
-- url     : https://prove2.me/theorems/2e072651-61b3-496a-aab5-3b3c465d5b26
-- title:
--   Lemma 3.2 — $\mathrm{Tr}[AM^\rho]\le\max_g\mathrm{Tr}[AM^g]+2\|A\|_*$
-- statement:
--   Fix a CAR system on $n\ge2$ modes. For every density matrix $\rho$ and every real symmetric coefficient matrix $A\in\mathbb R^{E\times E}$,
--   $$\operatorname{Tr}[AM^\rho]\le\max_{|g\rangle\ \text{Gaussian}}\operatorname{Tr}[AM^g]+2\|A\|_*,$$
--   where $\|A\|_*$ is the nuclear norm (sum of absolute values of the eigenvalues of $A$).
--
--   The energy of any state for the quartic Hamiltonian $H_A$ is thus within $2\|A\|_*$ of the best Gaussian energy; Proposition 3.3 removes the dependence of the Gaussian on $A$.
--
--   Differences from the source:
--   - encoding: max over Gaussian states → supremum over the (nonempty, bounded) set of values $\operatorname{Tr}[AM^g]$; "real symmetric" → `A.IsHermitian` over $\mathbb R$; reason: the maximum is attained (p.8), and Hermitian real matrices are the symmetric ones
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.12, Lemma 3.2, eq. (3.8); nuclear norm p.11

import Mathlib
import Definitions.Def_QuarticGauss390_EigenBound_CAR
import Definitions.Def_QuarticGauss390_EigenBound_Gaussian
import Definitions.Def_QuarticGauss390_EigenBound_Moments
import Definitions.Def_QuarticGauss390_EigenBound_MatrixNorms

open Matrix

namespace QuarticGauss390.EigenBound

/-- Lemma 3.2, p.12: for every density matrix `ρ` and real symmetric coefficient matrix `A`,
`Tr[A M^ρ] ≤ max_{|g⟩ Gaussian} Tr[A M^g] + 2 ‖A‖_*` (3.8). -/
theorem lemma_3_2 {n : ℕ} (hn : 2 ≤ n) (C : CAR n) (ρ : Op n) (hρ : IsDensity ρ)
    (A : Matrix (Pair n) (Pair n) ℝ) (hA : A.IsHermitian) :
    (A * momentMatrix C ρ).trace ≤
      sSup {e : ℝ | ∃ g : Vec n, IsGaussian C g ∧
        e = (A * momentMatrix C (pureProj g)).trace} + 2 * nuclearNorm hA := by sorry

end QuarticGauss390.EigenBound
