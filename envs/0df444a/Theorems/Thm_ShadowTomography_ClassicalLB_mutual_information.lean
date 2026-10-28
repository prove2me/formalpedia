-- Prove2me | Theorems.Thm_ShadowTomography_ClassicalLB_mutual_information
-- name    : ShadowTomography.ClassicalLB.mutual_information
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:27:31.157116+00:00
-- url     : https://prove2.me/theorems/feff2903-bae8-4aef-a93a-6b617bc59d3c
-- title:
--   Mutual information of samples from the biased subset family
-- statement:
--   Let $K\ge1$ and let $S_i\subseteq[N]$, for $i\in[K]$, all have size $N/2\ge1$. Choose $i$ uniformly, then draw $T$ conditionally independent samples $X=(x_1,\ldots,x_T)$ from $\mathcal D_i=\mathcal D_{S_i,\varepsilon}$, where $0\le\varepsilon\le1/6$. For every $i$,
--
--   $$
--   I(X;i)\le T\bigl(\log_2 N-H(\mathcal D_i)\bigr).
--   $$
--
--   The bound limits how much the samples reveal about the hidden index in the lower-bound construction.
--
--   **Formalization Note** The theorem constructs finite distributions for the $\mathcal D_i$ and the joint law of $(X,i)$ with mass $K^{-1}\prod_t\mathcal D_i(x_t)$. Mutual information and entropy are the referenced `WildeQIT` definitions, measured in bits.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 21, proof of Theorem 16, mutual-information display

import Mathlib
import Definitions.Def_WildeQIT_mutualInfo
import Definitions.Def_ShadowTomography_ClassicalLB_biasedDist

namespace ShadowTomography.ClassicalLB

/-- The information bound for samples drawn independently from a uniformly selected
member of the half-subset family constructed on p. 20. -/
theorem mutual_information (K N T : ℕ) (hK : 1 ≤ K)
    (S : Fin K → Finset (Fin N)) (hhalf : ∀ i, 2 * (S i).card = N)
    (hne : ∀ i, 1 ≤ (S i).card) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 6) :
    ∃ P : Fin K → WildeQIT.FinDist (Fin N),
      (∀ i x, (P i).prob x = biasedDist N (S i) ε x) ∧
      ∃ J : WildeQIT.FinDist ((Fin T → Fin N) × Fin K),
        (∀ x i, J.prob (x, i) = (1 / (K : ℝ)) * ∏ t : Fin T, (P i).prob (x t)) ∧
        ∀ i, WildeQIT.mutualInfo J ≤
          (T : ℝ) * (Real.logb 2 N - WildeQIT.entropy (P i)) := by sorry

end ShadowTomography.ClassicalLB
