-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P48_beam_splitter_ordering
-- name    : QAlgorithms.Papers.Independent.Support50.P48.beam_splitter_ordering
-- status  : Open
-- author  : @Goku
-- created : 2026-10-24T00:02:47.754654+00:00
-- url     : https://prove2.me/theorems/0bc2dc48-84a2-495b-9f18-d0d38efc61fc
-- title:
--   Any ordering of output ports realizes the same vacuum broadcast channel
-- statement:
--   Let $m\ge1$ and let the $m+1$ receiver and environment port weights $\eta_i\ge0$ sum to one. Fix any ordering $\pi$ of these ports. There exist $m$ continuing-port transmissivities $t_j\in[0,1]$ such that, whenever the residual intensity $r_j=1-\sum_{k<j}\eta_{\pi(k)}$ is positive,
--
--   $$
--   t_j=\frac{r_j-\eta_{\pi(j)}}{r_j}.
--   $$
--
--   The successive vacuum beam splitters have exactly the same full number-basis amplitudes as the single-input vacuum splitting isometry with port amplitudes $\sqrt{\eta_i}$. Their output density operators therefore agree for every normal input, including arbitrary reference systems. At stages with zero residual intensity the remaining ports carry vacuum, so their splitter parameters can be chosen freely in $[0,1]$.
--
--   This permits the port reorderings used in the broadcast-cut converse. **Formalization Note** Stages are zero-indexed. A positive signal-amplitude phase convention is fixed for all output ports; fixed local phase rotations recover the source convention, including the negative Charlie coefficient in (2). The environment remains in the equality, so tracing it also gives equal broadcast outputs.
-- source:
--   Unconstrained distillation capacities of a pure-loss bosonic broadcast channel, arXiv:1601.05563v3, PDF p. 6, Appendix Fig.3 and (30); alternative realizations, p.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P48

open Filter

open scoped BigOperators ENNReal NNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P30
  (PureLossBroadcastParameters thermalEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, alternative realizations; PDF p.6, Fig.3 and (30).
For any ordering of all receiver/environment ports there are m physical vacuum
splitters with the printed continuing-port fractions at active stages. At zero
residual intensity any [0,1] continuation works. Equality holds on the full
referenced channel, without a photon cutoff; fixed local output phases match
(1)-(3). Here eta includes the environment and therefore sums to one. -/
theorem beam_splitter_ordering {m : ℕ} (hm : 0 < m)
    (eta : Fin (m + 1) → ℝ≥0) (heta : (∑ i, eta i) = 1)
    (order : Equiv.Perm (Fin (m + 1))) :
    ∃ t : Fin m → ℝ,
      (∀ j, 0 ≤ t j ∧ t j ≤ 1) ∧
      (∀ j, 0 < residualIntensity eta order j.val →
        t j = residualIntensity eta order (j.val + 1) /
          residualIntensity eta order j.val) ∧
      (∀ out n, sequentialAmplitude t order out n = vacuumAmplitude eta out n) ∧
      (∀ (R : Type) (rho : State (R × ℕ)),
        IsDensity (referencedVacuumOutput (sequentialAmplitude t order) rho.coefficients) ∧
        referencedVacuumOutput (sequentialAmplitude t order) rho.coefficients =
          referencedVacuumOutput (vacuumAmplitude eta) rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Support50.P48

end
