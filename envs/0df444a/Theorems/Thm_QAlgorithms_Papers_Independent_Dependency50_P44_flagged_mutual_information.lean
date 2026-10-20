-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P44_flagged_mutual_information
-- name    : QAlgorithms.Papers.Independent.Dependency50.P44.flagged_mutual_information
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:32:15.625039+00:00
-- url     : https://prove2.me/theorems/e41d1d7b-f8f6-44e0-9264-01b1478c6a9d
-- title:
--   Mutual information of a classically flagged pure state
-- statement:
--   Let $A,B,C,D$ be finite-dimensional nonzero complex Hilbert spaces with fixed bases on $B,D$. Let $f$ be any function from the basis labels of $D$ to those of $B$, let $\alpha_i\in\mathbb C$, and let $\mu_i^A,\nu_i^C$ be arbitrary unit vectors. Suppose the vector
--
--   $$|\xi\rangle^{ABCD}=\sum_i\alpha_i|\mu_i\rangle^A\otimes|f(i)\rangle^B\otimes|\nu_i\rangle^C\otimes|i\rangle^D$$
--
--   has norm one. Then its computed reduced density matrices satisfy
--
--   $$I(A;B)_\xi\le H(B)_\xi.$$
--
--   Entropy and mutual information are in bits. Neither injectivity nor surjectivity of $f$, nor orthogonality of the component states, is required. The orthogonal flag on $D$ and the vector's normalization encode exactly the classically indexed pure state used in the source.
-- source:
--   A father protocol for quantum broadcast channels, arXiv:quant-ph/0612155v4, PDF p. 7, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF p.7, Lemma 2: mutual information of the constructed classically indexed state is at
most the output entropy. Normalization of alpha is enforced by the norm of the actual vector. -/
theorem flagged_mutual_information {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (f : D → B) (alpha : D → ℂ) (mu : D → EuclideanSpace ℂ A)
    (nu : D → EuclideanSpace ℂ C) (hmu : ∀ i, ‖mu i‖ = 1) (hnu : ∀ i, ‖nu i‖ = 1)
    (hnorm : ‖flaggedVector f alpha mu nu‖ = 1) :
    let rho := pureDensity (flaggedVector f alpha mu nu)
    let rhoAB := regroupPartialTrace (fun x : A × (B × (C × D)) => (x.1, x.2.1))
      (fun x => x.2.2) rho
    let rhoA := traceRight rhoAB
    let rhoB := traceLeft rhoAB
    vnEntropy rhoA + vnEntropy rhoB - vnEntropy rhoAB ≤ vnEntropy rhoB := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P44

end
