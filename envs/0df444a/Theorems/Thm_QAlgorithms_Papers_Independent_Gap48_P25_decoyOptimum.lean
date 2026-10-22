-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_decoyOptimum
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.decoyOptimum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:44:45.426984+00:00
-- url     : https://prove2.me/theorems/f628a5be-5ee6-4e1f-8cce-f086e2651ea0
-- title:
--   IV.B.4: approximate decoy optimization, Eqs.(38)–(39)
-- statement:
--   Let $\widetilde\nu_S>0$ and $s\in(0,1]$, $Q\in[0,1]$ and $h=h(Q)<1/2$, in bits. Under the source's honest-rate, exact-parameter, dominant-intensity decoy estimate with perfect error correction and negligible dark counts, replacing $e^{-\mu}$ by $1-\mu$ gives $q(\mu)=\widetilde\nu_Ss\mu[(1-\mu)(1-h)-h]$. Its unique maximum on $\mu\ge0$ is
--
--   $$\mu_*={1\over2}\left(1-{h\over1-h}\right)>0,\qquad \max q={\widetilde\nu_Ss\mu_*(1-2h)\over2}.$$
--
--   The other root is $2\mu_*$ and the optimized proxy is linear in $s$, hence in line transmission with other factors fixed. These are statements about the quadratic approximation, not arbitrary physical operating intensities.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 30, IV.B.4: approximate decoy optimization, Eqs.(38)–(39)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eqs.(38)–(39), PDF p.30: decoy proxy optimizer, critical root and linear scaling. -/
theorem decoyOptimum (nu s Q : ℝ) (hnu : 0 < nu) (hs : 0 < s) (hs1 : s ≤ 1)
    (hQ : Q ∈ Set.Icc (0 : ℝ) 1) (hh : QAlgorithms.binEntropy2 Q < 1/2) :
    0 < decoyOptimizer Q ∧
    decoyProxy nu s Q (decoyOptimizer Q) = nu*s*decoyOptimizer Q*(1-2*QAlgorithms.binEntropy2 Q)/2 ∧
    (∀ mu : ℝ, 0 ≤ mu → decoyProxy nu s Q mu ≤ decoyProxy nu s Q (decoyOptimizer Q)) ∧
    (∀ mu : ℝ, 0 ≤ mu → (decoyProxy nu s Q mu =
      decoyProxy nu s Q (decoyOptimizer Q) ↔ mu = decoyOptimizer Q)) ∧
    decoyProxy nu s Q (2*decoyOptimizer Q) = 0 ∧
    (∀ t b : ℝ, decoyProxy nu (t*b) Q (decoyOptimizer Q) = t*decoyProxy nu b Q (decoyOptimizer Q)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
