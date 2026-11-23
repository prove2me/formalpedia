-- Prove2me | Theorems.Thm_SameStatePairs_top_k_rank_deficient
-- name    : SameStatePairs.top_k_rank_deficient
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T21:05:26.51492+00:00
-- url     : https://prove2.me/theorems/06079254-ef19-460f-99c8-a39c4cadb411
-- title:
--   Theorem 1 (rank below $k$, and $\varepsilon = 0$): no kernel direction is identified
-- statement:
--   In the setting of Theorem 1 (finite world and observation space, $p>0$, $P_X>0$, $k\ge1$), with $r=\operatorname{rank}(T_s)$ on the centred subspace:
--
--   1. If $r<k$, then for every $0<\varepsilon\le1$:
--      - the top-$k$ sum is the sum of all positive eigenvalues: $\sum_{i=1}^k\lambda_i=\sum_{i:\lambda_i>0}\lambda_i$;
--      - the span of every global minimiser of $L_\varepsilon$ contains the positive eigenspace $E_+$ and equals $E_+\oplus W$ for some $(k-r)$-dimensional subspace $W$ of $\ker T_s$;
--      - for every $(k-r)$-dimensional subspace $W$ of $\ker T_s$ there is a global minimiser with span $E_+\oplus W$.
--   2. At $\varepsilon=0$, $L_0(f)=2k$ for every centred, whitened $f$.
--
--   So in the rank-deficient case no direction in the kernel is identified, and at $\varepsilon=0$ no direction is identified at all.
--
--   **Formalization Note** $E_+$ and $\ker T_s$ are taken on the centred subspace. The sum over positive eigenvalues runs over the indices $1\le i\le|X|-1$. The informal conclusions "no direction is identified/identifiable" are not separate formal claims; they are the content of the stated items.
-- source:
--   Xin Li, Same-State Pairs Make One JEPA Proof of the Platonic Representation Hypothesis Vacuous: A Correction and a Gauge Ledger, arXiv:2611.16182v1 (2026), Section 4.1, Theorem 1, eq. (3), p. 6; proof in Appendix A.1, p. 11

import Mathlib
import Definitions.Def_SameStatePairs_Basic

open Matrix

namespace SameStatePairs

theorem top_k_rank_deficient {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq X] {k : ℕ}
    (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1)
    (κ : Z → X → ℝ) (hκ : IsChannel κ) (hX : ∀ x, 0 < obsLaw p κ x) (hk : 1 ≤ k) :
    (obsRank p κ < k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∑ i ∈ Finset.Icc 1 k, obsEig p κ i =
        ∑ i ∈ (Finset.Icc 1 (Fintype.card X - 1)).filter (fun i => 0 < obsEig p κ i),
          obsEig p κ i) ∧
      (∀ f : X → Fin k → ℝ, IsGlobalMin (obsLaw p κ) (mixPairLaw p κ ε) f →
        posSpace p κ ≤ coordSpan f ∧
        ∃ W : Submodule ℝ (X → ℝ), W ≤ obsKerSpace p κ ∧
          Module.finrank ℝ W = k - obsRank p κ ∧ coordSpan f = posSpace p κ ⊔ W) ∧
      (∀ W : Submodule ℝ (X → ℝ), W ≤ obsKerSpace p κ → Module.finrank ℝ W = k - obsRank p κ →
        ∃ f : X → Fin k → ℝ, IsGlobalMin (obsLaw p κ) (mixPairLaw p κ ε) f ∧
          coordSpan f = posSpace p κ ⊔ W)) ∧
    (∀ f : X → Fin k → ℝ, IsCentered (obsLaw p κ) f → IsWhitened (obsLaw p κ) f →
      pairLoss (mixPairLaw p κ 0) f = 2 * k) := by sorry

end SameStatePairs
