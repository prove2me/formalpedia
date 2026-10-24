-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P18_entropy_continuity_29
-- name    : QAlgorithms.Papers.Independent.Support50.P18.entropy_continuity_29
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:22:16.407952+00:00
-- url     : https://prove2.me/theorems/8a76a660-dc91-4c8f-ad2d-44b48bea41c0
-- title:
--   Section 5.1: entropy continuity bound (29)
-- statement:
--   Let $A,B$ be separable systems and let the nonnegative self-adjoint Hamiltonian $H_A$ satisfy $\lim_{\lambda\downarrow0}(\operatorname{Tr}e^{-\lambda H_A})^\lambda=1$. Work in a complete energy eigenbasis; the hypothesis itself guarantees a discrete spectrum. Write $E_0=\inf_{\|u\|=1}\langle u,H_Au\rangle$ and $F_{H_A}(u)=\sup_{\operatorname{Tr}H_A\tau\le u}H(\tau)$. These suprema are finite for finite $u\ge E_0$, and the $A$ entropy is finite throughout each energy ball. For $E\ge E_0$, joint states with both $A$ energies at most $E$, and $0<\varepsilon=\frac12\|\rho-\sigma\|_1\le1/2$,
--
--   $$|H(\rho_A)-H(\sigma_A)|\le\sqrt{2\varepsilon}\,F_{H_A}(E/\varepsilon)+g(\sqrt{2\varepsilon}).$$
--
--   This specializes the AFW estimate to entropy; no entropy condition is placed on $B$.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, PDF p. 11, Section 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P18

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P18

open QAlgorithms.Papers.Independent.Dependency50.P33 (State PureState traceSize rankOne)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Renew46.P08
  (coefficientEnergy entropySupremum extendedHalfTraceDistance)

/-- Section 5.1, PDF p.11, (29). Condition (22) is inherited from Proposition 2.
Finiteness precedes all real conversions; epsilon is the stated joint trace distance. -/
theorem entropy_continuity_29 {I J : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (energy : I → ℝ≥0) (h22 : Condition22 energy)
    (E : ℝ) (hE : spectralGround energy ≤ E) :
    (∀ u : ℝ, spectralGround energy ≤ u → entropySupremum energy u < ⊤) ∧
    (∀ rho : State (I × J),
      coefficientEnergy energy (traceSecond rho.coefficients) ≤ ENNReal.ofReal E →
      extendedEntropyNats (traceSecond rho.coefficients) < ⊤) ∧
    ∀ (rho sigma : State (I × J)) (eps : ℝ),
      coefficientEnergy energy (traceSecond rho.coefficients) ≤ ENNReal.ofReal E →
      coefficientEnergy energy (traceSecond sigma.coefficients) ≤ ENNReal.ofReal E →
      0 < eps → eps ≤ 1 / 2 → nuclearStateDistance rho sigma = ENNReal.ofReal eps →
      |(extendedEntropyNats (traceSecond rho.coefficients)).toReal -
        (extendedEntropyNats (traceSecond sigma.coefficients)).toReal| ≤
        entropyModulus (entropySupremum energy) 1 1 E eps := by sorry

end QAlgorithms.Papers.Independent.Support50.P18

end
