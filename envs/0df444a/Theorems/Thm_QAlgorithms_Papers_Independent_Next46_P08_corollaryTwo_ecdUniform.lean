-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P08_corollaryTwo_ecdUniform
-- name    : QAlgorithms.Papers.Independent.Next46.P08.corollaryTwo_ecdUniform
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:55:03.580295+00:00
-- url     : https://prove2.me/theorems/b697c6c7-d9a3-4277-a405-4a5241d24c24
-- title:
--   Corrected Corollary 2: ECD-uniform continuity of block mutual information
-- statement:
--   Let $A,B,H_A,H_B,E_0^A,E_0^B$ satisfy the spectral assumptions of the corrected first corollary: $A,B$ are infinite-dimensional separable complex systems, $H_A$ is positive with discrete finite-multiplicity spectrum tending to infinity, and $H_B$ is positive with finite Gibbs trace at every positive inverse temperature. Let $n\ge1$, let $C$ be any nonzero separable system, and let $\rho$ be any normalized state on $A^{\otimes n}\otimes C$ with $\max_{1\le k\le n}\operatorname{Tr}H_A\rho_{A_k}<\infty$. Fix $E>E_0^B$ and $L>E_0^A$, and use the full ancilla-supremum ECD distance $D_L$ at the input level $L$. Define
--
--   $$
--   \mathcal F_{\rho,E}=\left\{\Phi:\frac1n\sum_{k=1}^n\operatorname{Tr}H_B\Phi(\rho_{A_k})\le E\right\},\qquad
--   J_\rho(\Phi)=I(B^n:C)_{(\Phi^{\otimes n}\otimes\mathrm{Id}_C)(\rho)}.
--   $$
--
--   The mutual information $J_\rho$ is finite on this set, and
--
--   $$
--   \forall\eta>0\ \exists\delta>0\ \forall\Phi,\Psi\in\mathcal F_{\rho,E},\quad
--   D_L(\Phi,\Psi)<\delta\ \Longrightarrow\ |J_\rho(\Phi)-J_\rho(\Psi)|<\eta.
--   $$
--
--   The reference has no dimension or energy constraint. The output constraint is a mean, not a maximum. This corrects the metric-independent wording to the specified ECD uniformity.
--
--   **Formalization Note** All marginal states, the maximum input energy, the mean output energy, and the channel tensor power are computed from $\rho$. The quantum mutual information is extended relative entropy to the actual product of marginals; its finiteness is concluded before real conversion.
-- source:
--   Energy-constrained diamond norms and their use in quantum information theory, arXiv:1706.00361v2, PDF p. 13, Corollary 2: explicitly corrected ECD-uniform content

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P08

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P08

export QAlgorithms.Papers.Independent.Claimed50.P32 (StrongChannel)

export QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble ensembleHolevo)

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Corollary 2, PDF p.13: corrected ECD-uniform content with arbitrary
nonzero separable reference, every positive block length and MEAN output
energy. Printed: every compatible metric via footnote 8 and Remark 4.
Changed: each specified ECD distance. Reason: uniformity is not determined
by a topology. QMI finiteness is concluded before taking real differences. -/
theorem corollaryTwo_ecdUniform
    (energyA energyB : ℕ → ℝ≥0)
    (hA : QAlgorithms.Papers.Independent.Claimed50.P32.IsEnergyOperator energyA)
    (hB : EigenbasisGibbsCondition energyB) (n : ℕ) (hn : 0 < n)
    {C : Type} [Countable C] [Nonempty C]
    (rho : Nuclear.State ((Fin n → ℕ) × C))
    (hrho : maxInputEnergy energyA rho < ⊤)
    (E : ℝ) (hE : eigenbasisGroundEnergy energyB < E)
    (L : ℝ) (hL : eigenbasisGroundEnergy energyA < L) :
    (∀ Phi : StrongChannel ℕ ℕ, meanOutputEnergy energyB Phi rho ≤ ENNReal.ofReal E →
      blockMutualInformation Phi rho < ⊤) ∧
    (∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
      ∀ Phi Psi : StrongChannel ℕ ℕ,
        meanOutputEnergy energyB Phi rho ≤ ENNReal.ofReal E →
        meanOutputEnergy energyB Psi rho ≤ ENNReal.ofReal E →
        ecdMagnitude energyA L Phi Psi < ENNReal.ofReal delta →
        |(blockMutualInformation Phi rho).toReal -
          (blockMutualInformation Psi rho).toReal| < eta) := by sorry

end QAlgorithms.Papers.Independent.Next46.P08

end
