-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P41_extraction_information_properties
-- name    : QAlgorithms.Papers.Independent.Advance50.P41.extraction_information_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:10:33.007607+00:00
-- url     : https://prove2.me/theorems/5c5b01b0-2d4f-4743-8103-4e533c1ff96c
-- title:
--   Five properties of reversible extraction information
-- statement:
--   Let $\mathcal E=\{p(x),|\psi_x\rangle^A\otimes|\sigma_x\rangle^C\}$ be a countably supported ensemble with strictly positive probabilities summing to one and normalized pure vectors on finite-dimensional complex systems $A,C$. Let $Y=y(X)$ be the canonical orthogonal irreducible-component label of the joint $AC$ ensemble. Entropies $S$ use base-two logarithms and refer to the resulting source and its canonical $Y$ extension.
--
--   For $\epsilon\ge0$, let $I_\epsilon(\omega)$ be the maximum of $I(X:\widehat CW)$ over isometries $AC\to\widehat A\widehat CW$ whose average retained joint root fidelity is at least $1-\epsilon$. Then:
--
--   1. $I_\epsilon(\omega)$ is nondecreasing in $\epsilon$.
--   2. For $\epsilon_1,\epsilon_2\ge0$ and $0\le\lambda\le1$,
--   $$\lambda I_{\epsilon_1}(\omega)+(1-\lambda)I_{\epsilon_2}(\omega)\le I_{\lambda\epsilon_1+(1-\lambda)\epsilon_2}(\omega).$$
--   3. The function is continuous on $[0,\infty)$, including right continuity at zero.
--   4. For two such product-pure sources and the same $\epsilon\ge0$,
--   $$I_\epsilon(\omega_1\otimes\omega_2)\le I_\epsilon(\omega_1)+I_\epsilon(\omega_2).$$
--   5. On the canonical extension,
--   $$I_0(\omega)\le S(CY).$$
--
--   These properties control the information term in the quantum-rate converse.
-- source:
--   Entanglement-Assisted Quantum Data Compression, arXiv:1901.06346v1, PDF p. 3, Lemma 5

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P41

open Filter

open scoped Topology BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A C : Type} [Fintype A] [Fintype C]

/-- Lemma 5, PDF p.3: all five clauses. Continuity is relative to [0,infinity),
including right continuity at zero; tensor subadditivity uses the SAME eps.
The tensor source uses the constructed independent product law. -/
theorem extraction_information_properties [Countable X] (s : ProductPureSource X A C) (hs : s.Valid) :
    MonotoneOn (extractionInformation s) (Set.Ici 0) ∧
    (∀ eps1 eps2 lam : ℝ, 0 ≤ eps1 → 0 ≤ eps2 → 0 ≤ lam → lam ≤ 1 →
      lam * extractionInformation s eps1 + (1 - lam) * extractionInformation s eps2 ≤
        extractionInformation s (lam * eps1 + (1 - lam) * eps2)) ∧
    ContinuousOn (extractionInformation s) (Set.Ici 0) ∧
    (∀ (X2 A2 C2 : Type) [Countable X2] [Fintype A2] [Fintype C2]
      (t : ProductPureSource X2 A2 C2), t.Valid →
      ∀ eps : ℝ, 0 ≤ eps →
        extractionInformation (productSource s t) eps ≤
          extractionInformation s eps + extractionInformation t eps) ∧
    extractionInformation s 0 ≤ s.entropyCY := by sorry

end QAlgorithms.Papers.Independent.Advance50.P41

end
