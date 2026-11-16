-- Prove2me | Theorems.Thm_StableVotingDistortion_Supplement_theorem_8
-- name    : StableVotingDistortion.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:58:36.001212+00:00
-- url     : https://prove2.me/theorems/f64f6f37-8f61-443a-a8a0-45e02d3953f1
-- title:
--   Theorem 8 — for every integer $k>1$ the supremum distortion of stable $k$-lotteries is exactly $1+2\lambda_k$
-- statement:
--   For every integer $k>1$, the supremum of the metric distortion over all elections and their stable $k$-lotteries is $1+2\lambda_k$, where
--   $$
--   \lambda_k=\frac{1+(k-1)(k+1)^{-1/(k-1)}}{k}.
--   $$
--   Explicitly:
--
--   1. in every election every stable $k$-lottery has distortion at most $1+2\lambda_k$;
--   2. for every $B<1+2\lambda_k$ there are an election and a stable $k$-lottery $D$ of it, a consistent pseudometric $d$ and a candidate $a$ with $\mathrm{cost}_d(D)>B\cdot\mathrm{cost}_d(a)$.
--
--   The supremum need not be attained. The theorem shows that the bound of Theorem 6 is tight for every $k>1$.
--
--   **Formalization Note** Distortion is the base mission's inequality form; the elections in part 2 are finite elections with at least one voter and one candidate.
--
--   Differences from the source:
--
--   - encoding: distortion as a ratio cost_d(D)/min_a cost_d(a) → the base mission inequality HasDistortionAtMost: cost_d(D) ≤ B·cost_d(a) for every consistent pseudometric d and candidate a; reason: the base mission published convention (R3); agrees with the ratio whenever min_a cost_d(a) > 0
--   - encoding: some election (finite voter and candidate sets) → an election on Fin (n + 1) voters and Fin (m + 1) candidates; reason: every finite nonempty election is one of these up to relabeling
--   - encoding: the supremum of the distortion is 1 + 2λ_k → two conjuncts: 1 + 2λ_k is a valid bound, and no B < 1 + 2λ_k is; reason: the definition of a supremum
--   - encoding: λ_k with a real power → lambdaK k (k > 1 branch); reason: same values
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 8, p.38

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost
import Definitions.Def_StableVotingDistortion_Supplement_IsStableKLottery
import Definitions.Def_StableVotingDistortion_Supplement_lambdaK

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion.Supplement

/-- **Theorem 8.** For every integer `k > 1`, the supremum of the metric distortion over all elections and their
stable `k`-lotteries is `1 + 2λ_k`, `λ_k = (1 + (k − 1)(k + 1)^{−1/(k−1)})/k`: every stable `k`-lottery of every
election has distortion at most `1 + 2λ_k`, and for every `B < 1 + 2λ_k` some election has a stable `k`-lottery
whose distortion exceeds `B`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 8, p.38: "For every integer k > 1, the
supremum of the metric distortion over all elections and their stable k-lotteries is 1 + 2λk where
λk = (1 + (k −1)(k + 1)^{−1/(k−1)})/k."

**Formalization Note.** "The supremum is `1 + 2λ_k`" is the two conjuncts: an upper bound and no smaller bound.
Distortion is the inequality form `HasDistortionAtMost`; `¬ HasDistortionAtMost E D B` means some consistent
pseudometric and candidate violate the bound `B`. The supremum need not be attained. The elections of the
second conjunct are genuine finite elections, on `Fin (n + 1)` voters and `Fin (m + 1)` candidates (every finite
nonempty election up to relabeling). -/
theorem theorem_8 (k : ℕ) (hk : 1 < k) :
    (∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C) (D : C → ℝ),
        IsStableKLottery k E D → HasDistortionAtMost E D (1 + 2 * lambdaK k)) ∧
    (∀ B : ℝ, B < 1 + 2 * lambdaK k →
      ∃ (n m : ℕ) (E : Election (Fin (n + 1)) (Fin (m + 1))) (D : Fin (m + 1) → ℝ),
        IsStableKLottery k E D ∧ ¬ HasDistortionAtMost E D B) := by sorry

end StableVotingDistortion.Supplement
