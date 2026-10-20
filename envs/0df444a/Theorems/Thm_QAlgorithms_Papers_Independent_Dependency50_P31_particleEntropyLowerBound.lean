-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P31_particleEntropyLowerBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P31.particleEntropyLowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:34:36.792735+00:00
-- url     : https://prove2.me/theorems/254f1580-cb58-4f58-8332-d8efce5b0cff
-- title:
--   Lower bound on particle entanglement entropy
-- statement:
--   Let $\nu,N,d,W_\nu,c_l$ and $h_{(i,l)}$ be as in Theorem 1, with $N\ge2$ and $d\ge c_1$. Let $\psi\in W_\nu$ have norm one, and let $\rho_N=\operatorname{Tr}_{1,\ldots,N-1}|\psi\rangle\langle\psi|$. With natural logarithms, the entropy satisfies
--
--   $$
--   S(\rho_N)\ge\min_{(c_l,l)\in\mathcal R(\nu)}
--   \ln\left(\prod_{i=1}^{c_l-1}\frac{h_{(i,l)}}{h_{(i,l)}-1}\right).
--   $$
--
--   This is a lower bound on particle entanglement; general attainment is not asserted. An empty product contributes zero entropy.
--
--   **Formalization Note** Multiplying the frozen entropy in bits by $\ln2$ gives nats. A least element of the finite set of logarithmic products expresses the minimum.
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, PDF p. 6, Corollary 2, equation (16)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- Corollary 2, arXiv:1805.00364v2 PDF p.6, equation (16).
The lower bound is in nats and need not be attained. IsLeast expresses the finite minimum. -/
theorem particleEntropyLowerBound {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n)
    (psi : H d n) (hpsi : psi ∈ isotypicSpace nu) (hunit : ‖psi‖ = 1) :
    ∃ m : ℝ, IsLeast {r : ℝ | ∃ b, Removable nu.val b ∧ r = cornerEntropy nu.val b} m ∧
      m ≤ entropyNats psi := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P31

end
