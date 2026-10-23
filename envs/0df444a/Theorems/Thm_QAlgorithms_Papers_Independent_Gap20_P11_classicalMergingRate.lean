-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P11_classicalMergingRate
-- name    : QAlgorithms.Papers.Independent.Gap20.P11.classicalMergingRate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:15:59.490159+00:00
-- url     : https://prove2.me/theorems/2ecba564-d7e6-4917-9415-3205bc1c9cb0
-- title:
--   State merging simultaneously uses I(A:R) classical bits per copy
-- statement:
--   Let $|\psi\rangle_{RAB}$ be a normalized pure state of finite, nonzero-dimensional complex registers, with source density $\rho_{AB}=\operatorname{Tr}_R|\psi\rangle\langle\psi|$. All entropies use base two. For independent source copies, Alice can perform a finite-outcome quantum instrument and send its outcome to Bob, who applies a conditional local channel. The code depends on the source density, and no operation acts on $R$.
--
--   The source-only expression for the classical cost equals the actual Alice–reference mutual information:
--
--   $$
--   S(A)+S(A\mid B)=I(A:R)=S(A)+S(R)-S(AR).
--   $$
--
--   For every $\varepsilon,\delta>0$, every sufficiently large positive $n$ admits such a code with full joint trace-norm error at most $\varepsilon$ and an outcome alphabet of size $M_n$ satisfying
--
--   $$
--   \log_2 M_n\le n\bigl(I(A:R)+\delta\bigr),\qquad
--   k_n-\ell_n\le n\bigl(S(A\mid B)+\delta\bigr).
--   $$
--
--   The same code has the separate Bell consumption and yield guarantees of optimal merging, and uses no initial Bell pairs when $S(A\mid B)<0$. The joint target includes the final Bell pairs. This is the communication cost of the stated LOCC construction; it is not a converse for protocols supplied with free quantum messages.
-- source:
--   Quantum information can be negative, arXiv:quant-ph/0505062v1, PDF p. 4, Unnumbered protocol rate: classical communication I(A:R)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P11

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3–4: the stated merging construction has classical communication
I(A:R), simultaneously with its optimal EPR cost/yield. The equality relates the
computed source-only expression to the actual reference marginal; no decoupling
or entropy-duality conclusion has been assumed as a hypothesis. -/
theorem classicalMergingRate {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi) :
    classicalCost (traceLeft (pureDensity psi)) = referenceInformation psi ∧
    MergingConstruction (traceLeft (pureDensity psi))
      (referenceInformation psi) (conditionalEntropy (traceLeft (pureDensity psi))) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P11

end
