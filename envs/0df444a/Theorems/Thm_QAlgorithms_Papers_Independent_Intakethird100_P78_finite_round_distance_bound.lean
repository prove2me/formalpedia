-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P78_finite_round_distance_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P78.finite_round_distance_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:16:35.42121+00:00
-- url     : https://prove2.me/theorems/90bea76b-87d8-4883-8877-d90de70a2703
-- title:
--   Strict finite-round total-variation bound with exact smaller resources
-- statement:
--   Let $X,Y$ be finite nonempty input alphabets and let $D_d$ be a permutation system with $d>2$ outputs on each side. Start with independent uniform local labels in $[d]$. Run $n\ge1$ rounds of the stated protocol using independent exact copies of the corrected resource $D'(D_d)$ and fresh shared coins, with retention probability $1/d$ in every round. Write $S_n$ for the resulting conditional output law.
--
--   With worst-input total variation defined by $\delta(S,D)=\max_{x,y}\frac12\sum_{a,b}|S(a,b\mid x,y)-D(a,b\mid x,y)|$, one has
--
--   $$
--   \delta(S_n,D_d)<\left(\frac{2}{d}\right)^n.
--   $$
--
--   This estimates the error of the explicitly defined finite-round construction. The source correction to equation (7) is inherited and awaits independent moderation.
-- source:
--   Bipartite Units of Non-Locality, arXiv:0808.0651v4, PDF p. 7, Unnumbered quantitative result (9): finite-round approximation using exact smaller resources

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P78

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P78

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, (9): positive n exact smaller-resource rounds give a strict
worst-input total-variation bound. The initial independent-uniform guess
is part of finiteRoundKernel. Uses corrected (7); independent moderation
of that source correction remains pending. -/
theorem finite_round_distance_bound
    {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    {m : ℕ} (hm : 1 < m)
    (F : X → Y → Equiv.Perm (Fin (m + 1)))
    (n : ℕ) (hn : 0 < n) :
    simulationDistance
      (finiteRoundKernel (lt_trans Nat.zero_lt_one hm) F n)
      (graphKernel (fun x y => F x y)) <
        (2 / ((m + 1 : ℕ) : ℝ)) ^ n := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P78

end
