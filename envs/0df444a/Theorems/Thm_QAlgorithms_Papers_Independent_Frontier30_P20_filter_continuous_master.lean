-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P20_filter_continuous_master
-- name    : QAlgorithms.Papers.Independent.Frontier30.P20.filter_continuous_master
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:48:29.339977+00:00
-- url     : https://prove2.me/theorems/582f7d69-423e-43bb-b79d-6d02cfae4fc7
-- title:
--   Unnumbered continuity-preserving filtering result, Eq.(31)
-- statement:
--   All maps act complex-linearly on the same matrix algebra $M_d(\mathbb C)$, where $d\ge1$. Composition $AB$ applies $B$ first. Norms of maps are induced by the unnormalized Hilbert–Schmidt norm. Let $L$ generate a continuous CPTP semigroup and let $T=Ae^LB$ be CPTP, where $A,B$ are invertible single-Kraus CP filters. There exist a continuous family $K(t)$ of CPTP semigroup generators on $[0,1]$ and its initial-value propagator $X$ such that
--
--   $$X(0)=\mathrm{id},\qquad X^{\prime}(t)=K(t)X(t),\qquad X(1)=T.$$
--
--   Derivatives at the endpoints are understood within $[0,1]$. The generator family is continuous up to both endpoints. This strengthens the filtering statement to an actual continuous time-dependent master equation for these filtered Markovian endpoints.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, PDF p. 16, Unnumbered continuity-preserving filtering result, Eq.(31)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.

local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- Unnumbered Eq.(31) result, PDF pp.15--16: continuous generators and an actual initial-value solution. -/
theorem filter_continuous_master {d : ℕ} (hd : 0 < d) (T A B L : Super d)
    (hT : Channel T) (hA : FilterMap A) (hB : FilterMap B)
    (hL : IsGenerator L) (hprod : T = A * NormedSpace.exp L * B) :
    ∃ K X : ℝ → Super d, ContinuousOn K (Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, IsGenerator (K t)) ∧ Propagates K X ∧ X 1 = T := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P20

end
