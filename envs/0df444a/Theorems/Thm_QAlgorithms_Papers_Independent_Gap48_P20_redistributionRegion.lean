-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_redistributionRegion
-- name    : QAlgorithms.Papers.Independent.Gap48.P20.redistributionRegion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:03:19.423688+00:00
-- url     : https://prove2.me/theorems/3c571f86-ea48-4dd2-8edc-f7b1d122a836
-- title:
--   Exact state-redistribution rate region and optimal corner
-- statement:
--   Let $A,C,B,R$ be nonzero finite-dimensional registers and let $|\psi\rangle^{ACBR}$ be a normalized pure state. Alice initially holds $AC$, Bob holds $B$, and $R$ is inaccessible. All entropies are von Neumann entropies in bits. Write
--   $$
--   Q_* = \tfrac12 I(C;R\mid B),\qquad E_* = \tfrac12[I(C;A)-I(C;B)].
--   $$
--   A rate pair $(Q,E)$ is achievable if, for every $\varepsilon,\delta>0$, every sufficiently large positive blocklength $n$ admits a finite local CPTP protocol with one forward quantum message of $q\le n(Q+\delta)$ qubits and initial and final Bell-pair counts $k,l$ satisfying $k-l\le n(E+\delta)$. Its joint output on $A^nC^nB^nR^n$ and both final Bell registers has full trace-norm distance at most $\varepsilon$ from $\psi^{\otimes n}\otimes\Phi_l$. No additional communication is free. In particular $Q\ge0$, while $E$ may be negative.
--
--   Then, for every real $Q,E$,
--   $$
--   (Q,E)\text{ is achievable}\quad\Longleftrightarrow\quad Q\ge Q_*\ \text{and}\ Q+E\ge H(C\mid B).
--   $$
--   Moreover $(Q_*,E_*)$ is achievable and $Q_*+E_*=H(C\mid B)$, so it simultaneously minimizes $Q$ and $Q+E$.
--
--   This gives the operational meaning of conditional mutual information. Finite forward protocols may be collected into an encoder and a decoder because there is no feedback.
-- source:
--   The operational meaning of quantum conditional information, arXiv:quant-ph/0612050v2, PDF p. 2, Main result: exact state-redistribution rate region and corner, Eqs. (1)–(2)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P20

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Main result, PDF p.2, region and (1)–(2): exact iff and the simultaneously
optimal corner. Costs are asymptotic rates, never exact finite-block equalities. -/
theorem redistributionRegion {A C B R : Type*}
    [Fintype A] [Fintype C] [Fintype B] [Fintype R]
    [Nonempty A] [Nonempty C] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (RedistributionSource A C B R)) (hpsi : IsState psi) :
    (∀ Q E : ℝ, RedistributionAchievable psi Q E ↔
      quantumCost psi ≤ Q ∧ conditionalCost psi ≤ Q + E) ∧
    RedistributionAchievable psi (quantumCost psi) (redistributionEntanglementRate psi) ∧
    quantumCost psi + redistributionEntanglementRate psi = conditionalCost psi ∧
    (∀ Q E : ℝ, RedistributionAchievable psi Q E →
      quantumCost psi ≤ Q ∧
        quantumCost psi + redistributionEntanglementRate psi ≤ Q + E) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P20

end
