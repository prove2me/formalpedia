-- Prove2me | Theorems.Thm_Viterbo_exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ
-- name    : Viterbo.exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T08:16:32.257236+00:00
-- url     : https://prove2.me/theorems/e8dc4ed9-e26b-42b9-bf6e-fdda32c73c30
-- title:
--   p. 2 — on convex domains the Ekeland–Hofer–Zehnder capacity is a minimal action and agrees with a symplectic capacity
-- statement:
--   For every $n \ge 1$ there is a symplectic capacity $c$ on $\mathbb R^{2n}$ (Definition 1.1) with $c(K) = c_{\rm EHZ}(K)$ for every convex domain $K \subset \mathbb R^{2n}$; and on every convex domain $K$ the infimum defining $c_{\rm EHZ}(K)$ is attained: some nonconstant generalized closed characteristic $\gamma$ on $\partial K$ has $|\mathcal A(\gamma)| = c_{\rm EHZ}(K)$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 2, the Ekeland–Hofer–Zehnder capacity as a symplectic capacity on convex domains, which cites Hofer, H. and Zehnder, E., A new capacity for symplectic manifolds, in Analysis, et cetera, Academic Press (1990) 405–427 (no DOI), and Ekeland, I. and Hofer, H., Symplectic topology and Hamiltonian dynamics, Math. Z. 200 (1989) 355–378, https://doi.org/10.1007/BF01215653

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

open scoped ENNReal

namespace Viterbo

theorem exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ (n : ℕ) (hn : 1 ≤ n) :
    (∃ c : Set (OAI.SymmetricPolar.Phase n) → ℝ≥0∞, IsSymplecticCapacity n c ∧
      ∀ K : Set (OAI.SymmetricPolar.Phase n), IsConvexDomain K → c K = cEHZ K) ∧
    ∀ K : Set (OAI.SymmetricPolar.Phase n), IsConvexDomain K →
      ∃ γ : ℝ → OAI.SymmetricPolar.Phase n, IsGeneralizedClosedCharacteristic K γ ∧
        (∃ s t, γ s ≠ γ t) ∧ cEHZ K = ENNReal.ofReal |action γ| := by
  sorry

end Viterbo
