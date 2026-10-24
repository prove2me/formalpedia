-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P48_ree_cut_limits
-- name    : QAlgorithms.Papers.Independent.Support50.P48.ree_cut_limits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-24T00:02:08.103459+00:00
-- url     : https://prove2.me/theorems/343360ee-92a9-4f6e-95dd-eb2c5a4fd35a
-- title:
--   Asymptotic relative entropy of entanglement across every receiver cut
-- statement:
--   Let $m\ge1$, $\eta_i\ge0$, $\sum_i\eta_i\le1$, and $\eta_E=1-\sum_i\eta_i$. Let $\phi^{(N)}_{AB_1\cdots B_m}$ be the actual output obtained by transmitting half of a TMSV with finite mean photon number $N\ge0$ through the vacuum pure-loss broadcast channel. For a nonempty receiver subset $T$, let $\bar T$ be its receiver complement. Relative entropy of entanglement is the infimum of quantum relative entropy in bits over all normal separable states, using trace-norm closed separability. Then
--
--   $$
--   \lim_{N\to\infty}E_R(T;A\bar T)_{\phi^{(N)}}=F(T),
--   $$
--
--   where $F(T)=0$ if $\eta_T=0$, $F(T)=+\infty$ if $\eta_T>0$ and $\eta_E=0$, and otherwise $F(T)=\log_2((\eta_E+\eta_T)/\eta_E)$, with $\eta_T=\sum_{i\in T}\eta_i$.
--
--   For two receivers the three nonempty cuts give (21), (25), and (26). This is an energy limit of actual resource-state REEs, not an exact finite-energy formula or a finite-energy operational converse.
-- source:
--   Unconstrained distillation capacities of a pure-loss bosonic broadcast channel, arXiv:1601.05563v3, PDF p. 4, (21), (25)-(26); Appendix (31), p.6

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

/-- PDF p.4, (21),(25)-(26); PDF p.6, (31), interpreted as an energy limit.
The printed numerator in (31) is 1-eta_complement(T), consistently with
(27) and the preceding line of (31); no numerator correction is made.
The limit is zero for a zero selected signal, and infinite for positive signal
with no loss, as inferred from the source proof at the allowed endpoints.
There is no exact finite-energy REE formula in this statement. -/
theorem ree_cut_limits {m : ℕ} (hm : 0 < m)
    (p : PureLossBroadcastParameters m) (T : Finset (Fin m)) (hT : T.Nonempty) :
    (∀ N : ℝ≥0, IsDensity (resourceCut p N T)) ∧
    Tendsto (fun N : ℝ≥0 => relativeEntanglementBits (resourceCut p N T))
      atTop (𝓝 (extendedCutBound p T)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P48

end
