-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P36_adjacentUseInterleaving
-- name    : QAlgorithms.Papers.Independent.Bridge50.P36.adjacentUseInterleaving
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:15:37.544299+00:00
-- url     : https://prove2.me/theorems/98d0bf8b-6c3b-491a-abe4-183d83f382aa
-- title:
--   Unbounded adjacent-use interleaving of private and coherent information
-- statement:
--   For every nonnegative integer $n$, there is a quantum channel $\mathcal N_n$ between nonzero finite-dimensional registers such that, for every integer $k$ with $1\le k<n$,
--
--   $$
--   \frac{P^{(1)}(\mathcal N_n^{\otimes k})}{k}<\frac{Q^{(1)}(\mathcal N_n^{\otimes(k+1)})}{k+1}.
--   $$
--
--   Here $Q^{(1)}(\mathcal N)=\max_\rho[H(B)-H(E)]$ and $P^{(1)}(\mathcal N)=\sup_{\{p_x,\rho_x\}}[I(X;B)-I(X;E)]$. Inputs are normalized positive semidefinite states, finite ensembles may contain mixed states, and $E$ is the entire complementary output of the same Stinespring isometry. Entangled inputs across uses are allowed; all entropies are in bits. One channel is chosen after $n$ and before all $k$.
--
--   This interleaves the two unregularized information rates through any prescribed finite number of uses. The conditions for $n=0,1$ are vacuous and still require a physical channel witness.
-- source:
--   Superadditivity of private information for any number of uses of the channel, arXiv:1502.05326v1, PDF p. 2, Theorem 1, (10)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P36

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory

-- These imports are pinned accepted libraries, permitted by the repair task.
-- P08.Ensemble allows an impossible zero-sized normalized ensemble; its total=1
-- field excludes that case without a separate positive-size field.

open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel maximumCoherentInformation dilationPower erasureDilation)

open QAlgorithms.Papers.Independent.Dependency50.P07 (accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P48 (privateMaximum)

variable {A B E C D : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]

variable [Fintype D] [DecidableEq D]

/-- Theorem 1, PDF p.2 (10), proved p.4: one physical channel, chosen after
n and before every k, strictly interleaves the adjacent-use information rates.
It is not asserted to work for every unbounded k. -/
theorem adjacentUseInterleaving (n : ℕ) :
    ∃ a b e : ℕ, 0 < a ∧ 0 < b ∧ 0 < e ∧
      ∃ V : Matrix (Fin b × Fin e) (Fin a) ℂ, Vᴴ * V = 1 ∧
        ∀ k : ℕ, 1 ≤ k → k < n →
          privateMaximum (dilationPower V k) / (k : ℝ) <
            maximumCoherentInformation (dilationPower V (k + 1)) / ((k + 1 : ℕ) : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P36

end
