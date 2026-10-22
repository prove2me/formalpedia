-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_perfectComposability
-- name    : QAlgorithms.Papers.Independent.Gap48.P20.perfectComposability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:05:54.315809+00:00
-- url     : https://prove2.me/theorems/4f6853a2-f0c7-4ddc-9522-792e62a4c49d
-- title:
--   Optimal successive redistribution of a composite system
-- statement:
--   Let $|\psi\rangle^{ACDBR}$ be normalized and pure on nonzero finite registers, with Alice initially holding $ACD$ and Bob holding $B$. Entropies are in bits. Define the joint-transfer costs and the costs of sending $D$ first and $C$ second by
--   $$
--   \begin{aligned}
--   Q&=\tfrac12 I(CD;R\mid B),&E&=\tfrac12[I(CD;A)-I(CD;B)],\\
--   Q_D&=\tfrac12 I(D;R\mid B),&E_D&=\tfrac12[I(D;AC)-I(D;B)],\\
--   Q_C&=\tfrac12 I(C;R\mid DB),&E_C&=\tfrac12[I(C;A)-I(C;DB)].
--   \end{aligned}
--   $$
--   Then
--   $$
--   Q=Q_C+Q_D,\qquad E=E_C+E_D.
--   $$
--   The joint corner $(Q,E)$ is achievable. Moreover finite protocols can transfer $D$ and then $C$ at their respective displayed rates: for every positive error and rate slack, all sufficiently large blocklengths admit both stages, each successful on its ideal source, whose actual composition reconstructs the complete source and both independent final Bell banks with vanishing joint full trace-norm error. Each stage has its own initial Bell bank and signed net consumption; negative $E_D$ or $E_C$ is allowed.
--
--   No Markov condition is required. Thus successive redistribution incurs no rate penalty relative to the joint optimum.
-- source:
--   The operational meaning of quantum conditional information, arXiv:quant-ph/0612050v2, PDF p. 2, perfect-composability

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P20

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)

attribute [local instance] Classical.propDecidable Classical.decEq

section Composite

variable {A C D B R : Type*}

variable [Fintype A] [Fintype C] [Fintype D] [Fintype B] [Fintype R]

/-- Perfect composability, PDF pp.2–3: both cost identities and a genuine
successive D-then-C protocol family at the joint optimal corner, without a
Markov hypothesis. -/
theorem perfectComposability [Nonempty A] [Nonempty C] [Nonempty D]
    [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × (C × (D × B))))) (hpsi : IsState psi) :
    quantumCost (jointSource psi) =
      quantumCost (secondSource psi) + quantumCost (firstSource psi) ∧
    redistributionEntanglementRate (jointSource psi) =
      redistributionEntanglementRate (secondSource psi) + redistributionEntanglementRate (firstSource psi) ∧
    RedistributionAchievable (jointSource psi) (quantumCost (jointSource psi))
      (redistributionEntanglementRate (jointSource psi)) ∧
    SuccessivelyAchievable psi (quantumCost (firstSource psi))
      (redistributionEntanglementRate (firstSource psi)) (quantumCost (secondSource psi))
      (redistributionEntanglementRate (secondSource psi)) := by sorry

end Composite

end QAlgorithms.Papers.Independent.Gap48.P20

end
