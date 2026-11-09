-- Prove2me | Theorems.Thm_TestingEstimation_Dense_label_optimum
-- name    : TestingEstimation.Dense.label_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:45.271824+00:00
-- url     : https://prove2.me/theorems/46d5c925-9d3b-4a55-84f9-7c624ac22f99
-- title:
--   Proposition 2 — label optimum and both conditional distance bounds
-- statement:
--   Fix $s=a+2\ge2$, $n\ge4s$, a property $P$, $0<\tau\le1/3$, and a symmetric rational rule satisfying both canonical guarantees at order $n$. Let $0<\gamma<1$ be real, $K=\binom s2$, $G$ an ordinary graph, and $\widetilde M(G)=\min_{z\in\Lambda^V}E_G(W_z)$ over all labelings. Then
--
--   $$M(G)\le\widetilde M(G)\le M(G)+(1+4K)\gamma.$$
--
--   The label minimum is attained. If additionally $P_n\ne\varnothing$, then
--
--   $$\operatorname{dist}(G,P)-\tau\le\widetilde M(G)\le\operatorname{dist}(G,P)+2\tau+(1+4K)\gamma.$$
--
--   The property-nonemptiness condition governs only the second comparison. Inconsistent labelings remain eligible for the minimization. This relates the finite optimization problem to the original distance.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
--   - encoding: sample size s at least 2 with anchors [3,s] → s=a+2 with anchors Fin a; reason: this bijective reindexing includes s=2 and its empty anchor set
--   - encoding: minimum or maximum → real infimum or supremum together with an explicit IsLeast or IsGreatest conclusion; reason: the conclusion includes attainment and excludes a replacement by a merely unattained extremal value
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Proposition 2, p. 15 (PDF 15)

import Definitions.Def_TestingEstimation_Dense_Labels

noncomputable section

namespace TestingEstimation.Dense

theorem label_optimum {a n : ℕ} (hn : 4*(a+2) ≤ n)
    (P : Property) (τ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ (1:ℝ)/3)
    (f : Rule (a+2)) (hf : SymmetricRule f) (hN2 : CanonicalGuarantees P τ n f)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 1) (G : Graph n) :
    minimumEnergy f G ≤ labelMinimum f γ G ∧
    labelMinimum f γ G ≤ minimumEnergy f G + (1 + 4*(Nat.choose (a+2) 2 : ℝ))*γ ∧
    IsLeast (Set.range (fun z : Fin n → Label a γ => energy f G (decoded f γ G z)))
      (labelMinimum f γ G) ∧
    ((P.graphs n).Nonempty →
      distance P G - τ ≤ labelMinimum f γ G ∧
      labelMinimum f γ G ≤ distance P G + 2*τ +
        (1 + 4*(Nat.choose (a+2) 2 : ℝ))*γ) := by sorry

end TestingEstimation.Dense
