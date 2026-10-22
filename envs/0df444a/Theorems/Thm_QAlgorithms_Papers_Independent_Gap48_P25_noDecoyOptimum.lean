-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_noDecoyOptimum
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.noDecoyOptimum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:43:55.229573+00:00
-- url     : https://prove2.me/theorems/23a8a24d-5256-48c9-b497-94fb4c334c9e
-- title:
--   IV.B.4: approximate no-decoy optimization, Eqs.(36)–(37)
-- statement:
--   Let $\widetilde\nu_S>0$ and $s\in(0,1]$, $0\le Q<1/4$, $A=1-h(2Q)>0$ and $F(Q)=1-h(2Q)-h(Q)\ge0$, with entropy in bits. Using the source's substitution $Q/Y_1\approx2Q$ only inside entropy defines the quadratic proxy $q(\mu)=\widetilde\nu_S[\mu sF(Q)-\mu^2 A/2]$. On $\mu\ge0$ its unique optimizer and maximum are
--
--   $$\mu_*={sF(Q)\over A},\qquad \max q={\widetilde\nu_Ss\mu_*F(Q)\over2}={\widetilde\nu_Ss^2F(Q)^2\over2A}.$$
--
--   Also $q(2\mu_*)=0$, including the degenerate $F=0$ case, where the optimizer is zero. The optimized proxy has quadratic transmission scaling. This is exact optimization of the displayed approximation, without a certified approximation error or an exact physical optimizing intensity.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 29, IV.B.4: approximate no-decoy optimization, Eqs.(36)–(37)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eqs.(36)–(37), PDF p.29: source quadratic's maximum and optimizer, with
informative entropy domain. The equality F=0 is allowed. -/
theorem noDecoyOptimum (nu s Q : ℝ) (hnu : 0 < nu) (hs : 0 < s) (hs1 : s ≤ 1)
    (hQ : 0 ≤ Q ∧ Q < 1/4) (hA : 0 < 1-QAlgorithms.binEntropy2 (2*Q))
    (hF : 0 ≤ noDecoyF Q) :
    0 ≤ noDecoyOptimizer s Q ∧
    noDecoyProxy nu s Q (noDecoyOptimizer s Q) = nu*s*noDecoyOptimizer s Q*noDecoyF Q/2 ∧
    (∀ mu : ℝ, 0 ≤ mu → noDecoyProxy nu s Q mu ≤ noDecoyProxy nu s Q (noDecoyOptimizer s Q)) ∧
    (∀ mu : ℝ, 0 ≤ mu → (noDecoyProxy nu s Q mu =
      noDecoyProxy nu s Q (noDecoyOptimizer s Q) ↔ mu = noDecoyOptimizer s Q)) ∧
    noDecoyProxy nu s Q (2*noDecoyOptimizer s Q) = 0 ∧
    noDecoyProxy nu s Q (noDecoyOptimizer s Q) =
      s^2*(nu*(noDecoyF Q)^2/(2*(1-QAlgorithms.binEntropy2 (2*Q)))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
