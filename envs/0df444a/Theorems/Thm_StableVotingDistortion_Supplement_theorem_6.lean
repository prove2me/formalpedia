-- Prove2me | Theorems.Thm_StableVotingDistortion_Supplement_theorem_6
-- name    : StableVotingDistortion.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:57:28.073716+00:00
-- url     : https://prove2.me/theorems/8e406def-83f3-4a8d-8826-ab0a4df08823
-- title:
--   Theorem 6 — stable $k$-lotteries have distortion at most $1+2\lambda_k$; exactly $7/3$ for $k=2,3$
-- statement:
--   For every integer $k\ge1$, in every election (finite nonempty voter and candidate sets) every stable $k$-lottery $D$ has metric distortion at most $1+2\lambda_k$, where
--   $$
--   \lambda_k=\frac{1+(k-1)(k+1)^{-1/(k-1)}}{k}\quad(k\ge2),\qquad \lambda_1=1 .
--   $$
--   That is, for every pseudometric $d$ on voters and candidates consistent with the election and every candidate $a$, $\mathrm{cost}_d(D)\le(1+2\lambda_k)\,\mathrm{cost}_d(a)$.
--
--   In particular, stable $2$-lotteries and stable $3$-lotteries have distortion $7/3\approx2.333$: for $k\in\{2,3\}$ every stable $k$-lottery of every election has distortion at most $7/3$, and for every $B<7/3$ some election has a stable $k$-lottery whose distortion exceeds $B$.
--
--   Stable $2$-lotteries are $3$-tournament rules, so this gives a simple rule with distortion well below $3$.
--
--   **Formalization Note** Distortion is the base mission's inequality form. The lower half of the "in particular" clause is Theorem 8 at $k=2,3$.
--
--   Differences from the source:
--
--   - encoding: distortion as a ratio cost_d(D)/min_a cost_d(a) → the base mission inequality HasDistortionAtMost: cost_d(D) ≤ B·cost_d(a) for every consistent pseudometric d and candidate a; reason: the base mission published convention (R3); agrees with the ratio whenever min_a cost_d(a) > 0
--   - encoding: λ_k with the power (k+1)^{−1/(k−1)} and λ_1 = 1 → lambdaK k, a real power, with the case k = 1 separately; reason: same values; λ_2 = λ_3 = 2/3 is proved in the sanity file
--   - reading: stable 2-lotteries and stable 3-lotteries have distortion 7/3 → for k ∈ {2, 3}: 7/3 is a distortion bound for every stable k-lottery of every election, and for every B < 7/3 some election (Fin (n+1) voters, Fin (m+1) candidates) has a stable k-lottery violating B; reason: the literal reading (distortion equal to 7/3), not the weaker "at most"; the lower half is the paper's Theorem 8 at k = 2, 3 ("The matching lower bound is proven in Appendix A by Theorem 8", p.14)
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 6, p.14

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_HasDistortionAtMost
import Definitions.Def_StableVotingDistortion_Supplement_IsStableKLottery
import Definitions.Def_StableVotingDistortion_Supplement_lambdaK

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion.Supplement

/-- **Theorem 6.** For every integer `k ≥ 1`, in any election every stable `k`-lottery has distortion at most
`1 + 2λ_k`; in particular stable `2`-lotteries and stable `3`-lotteries have distortion `7/3`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Theorem 6, p.14: "In any election, stable
k-lotteries have distortion at most 1 + 2λk where λk = (1 + (k −1)(k + 1)^{−1/(k−1)})/k and λ1 = 1. In
particular, stable 2-lotteries and stable 3-lotteries have distortion 7/3 ≈ 2.333."

**Formalization Note.** Distortion is the base mission's inequality form `HasDistortionAtMost`. The
"in particular" clause is the second conjunct, read literally: for `k = 2` and `k = 3` the distortion of stable
`k`-lotteries is `7/3`, i.e. `7/3` is a bound and no smaller `B` is (some finite election, on `Fin (n + 1)` voters
and `Fin (m + 1)` candidates, has a stable `k`-lottery violating `B`; this half is the paper's Theorem 8 at
`k = 2, 3`). -/
theorem theorem_6 :
    (∀ (k : ℕ), 1 ≤ k →
      ∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C) (D : C → ℝ),
        IsStableKLottery k E D → HasDistortionAtMost E D (1 + 2 * lambdaK k)) ∧
    (∀ k ∈ ({2, 3} : Finset ℕ),
      (∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C) (D : C → ℝ),
        IsStableKLottery k E D → HasDistortionAtMost E D (7 / 3)) ∧
      (∀ B : ℝ, B < 7 / 3 →
        ∃ (n m : ℕ) (E : Election (Fin (n + 1)) (Fin (m + 1))) (D : Fin (m + 1) → ℝ),
          IsStableKLottery k E D ∧ ¬ HasDistortionAtMost E D B)) := by sorry

end StableVotingDistortion.Supplement
