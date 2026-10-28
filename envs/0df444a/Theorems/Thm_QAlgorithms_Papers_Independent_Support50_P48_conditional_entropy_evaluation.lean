-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P48_conditional_entropy_evaluation
-- name    : QAlgorithms.Papers.Independent.Support50.P48.conditional_entropy_evaluation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-24T00:01:34.420836+00:00
-- url     : https://prove2.me/theorems/2223e1b0-7e04-476e-96dd-7c73f683232e
-- title:
--   Actual TMSV broadcast conditional entropies and their unconstrained limits
-- statement:
--   Let $m\ge1$, let $\eta_i\ge0$ with $\sum_i\eta_i\le1$, and put $\eta_E=1-\sum_i\eta_i$. For finite mean photon number $N\ge0$, send one half of the normalized two-mode squeezed vacuum through the vacuum pure-loss broadcast channel. Denote its purification by $\phi_{AB_1\cdots B_mE}$ and its reduced-state von Neumann entropies, in bits, by $H$. All of its subsystem entropies are finite. For every nonempty receiver subset $T$, write $\eta_T=\sum_{i\in T}\eta_i$ and let $\bar T$ be its receiver complement. Then
--
--   $$
--   -H(T\mid A\bar T)_\phi=H(A\bar T)_\phi-H(AB_1\cdots B_m)_\phi=H(TE)_\phi-H(E)_\phi=g((\eta_E+\eta_T)N)-g(\eta_E N),
--   $$
--
--   where $g(x)=(x+1)\log_2(x+1)-x\log_2x$ with $0\log_2 0=0$. As $N\to\infty$, this nonnegative difference converges in $[0,+\infty]$ to $F(T)$: zero if $\eta_T=0$, infinity if $\eta_T>0$ and $\eta_E=0$, and $\log_2((\eta_E+\eta_T)/\eta_E)$ otherwise.
--
--   This evaluates the actual resource-state conditional entropies used in the merging inner bound. **Formalization Note** The full Fock coefficients and actual partial traces are used; real entropy differences are accompanied by finiteness conclusions. Fixed local output phase rotations do not affect these entropies.
-- source:
--   Unconstrained distillation capacities of a pure-loss bosonic broadcast channel, arXiv:1601.05563v3, PDF p. 6, Appendix after (29); Section III.A, (12)-(13), p.3

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

/-- PDF p.3, entropy calculation and (12)-(13); PDF p.6, after (29).
All marginal entropies are finite for finite N. The conditional entropy is
computed from the actual TMSV output, not defined by the claimed g-difference.
The extended endpoint limit is inferred from that finite-energy difference. -/
theorem conditional_entropy_evaluation {m : ℕ} (hm : 0 < m)
    (p : PureLossBroadcastParameters m) (T : Finset (Fin m)) (hT : T.Nonempty) :
    (∀ N : ℝ≥0, IsDensity (purifiedResource p N) ∧
      (∀ S : Finset (ResourceMode m), resourceEntropyBits p N S ≠ ⊤) ∧
      reverseCutYield p N T =
        (resourceEntropyBits p N (environmentWith T)).toReal -
          (resourceEntropyBits p N (environmentWith ∅)).toReal ∧
      reverseCutYield p N T =
        thermalEntropyBits (((portWeight p none : ℝ) +
          (∑ i ∈ T, (p.transmissivity i : ℝ))) * (N : ℝ)) -
        thermalEntropyBits ((portWeight p none : ℝ) * (N : ℝ))) ∧
    Tendsto (fun N : ℝ≥0 => ENNReal.ofReal (reverseCutYield p N T))
      atTop (𝓝 (extendedCutBound p T)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P48

end
