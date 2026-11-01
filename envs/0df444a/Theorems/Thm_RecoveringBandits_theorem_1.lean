-- Prove2me | Theorems.Thm_RecoveringBandits_theorem_1
-- name    : RecoveringBandits.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:57:35.827687+00:00
-- url     : https://prove2.me/theorems/0c7b7085-920e-4da4-b80e-a95d487add99
-- title:
--   Theorem 1: every output of Algorithm 2 earns at least $\gamma_K\cdot\mathrm{UB}_R[K]\cdot T-O(N)$
-- statement:
--   There is an absolute constant $C$ such that for every admissible instance with $N$ arms and bound $R_{\max}$ and every capacity $K\ge1$:
--
--   1. Algorithm 2 has a run, i.e. some policy is an output of Algorithm 2;
--   2. every output $\pi$ of Algorithm 2 is a feasible $K$-PPP, and for every horizon $T\ge1$ its total reward satisfies
--
--   $$\mathrm{Reward}_T(\pi)\ \ge\ \gamma_K\cdot\mathrm{UB}_R[K]\cdot T-C\,N\,R_{\max},\qquad \gamma_K=\max_{a\in\mathbb Z_+}\frac{a}{a+1}\cdot\frac{K}{K+a}.$$
--
--   Since $\mathrm{UB}_R[K]\cdot T$ bounds the offline optimum (Lemma 2), the purely periodic policy of Algorithm 2 is a long-run $\gamma_K$-approximation, with $\gamma_K\ge1/4$ and $\gamma_K\to1$ as $K\to\infty$.
--
--   **Formalization Note** The first pull of each arm is measured from time $0$ (the arm's last pull before the start). The total reward is the sum of mean rewards, as in the objective of (1).
--
--   Differences from the source:
--   - reading: − O(N) → − C·N·Rmax for one absolute constant C chosen before the instance; reason: the proof (p.ec6) loses at most 2·R_i(d_i) ≤ 2·Rmax per selected arm, so C = 2
--   - generalization: the schedule returned by Algorithm 2 → every output of every run (any optimal x* with Lemma 2's property, any maximizer a*, any grouping, offsets and top-K selection), together with the existence of a run; reason: the paper's run is one of them
--   - generalization: the total reward of the schedule → also concludes that the output is a feasible K-PPP; reason: Algorithm 1's output is 'a feasible K-PPP' (line 2); an added conclusion
--   - generalization: K ≤ N (§2) → any K ≥ 1; reason: the bound does not need K ≤ N; specializes to it
--   - encoding: expected total reward; periods in Z+ ∪ {+∞} → sum of mean rewards R_i(gap); periods in WithTop ℕ; reason: the offline problem is deterministic in the means (p.7); same instances
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, Theorem 1, p.15; proof, p.ec6 (PDF p.38)

import Mathlib
import Definitions.Def_RecoveringBandits_Admissible
import Definitions.Def_RecoveringBandits_gamma
import Definitions.Def_RecoveringBandits_IsAlg2Run

namespace RecoveringBandits

/-- **Theorem 1**, Simchi-Levi–Zheng–Zhu, *Offline Planning and Online Learning under Recovering
Rewards*, arXiv:2106.14813v2, Theorem 1, p.15 (PDF p.15): for any `T ≥ 1`, the total reward of
the schedule returned by Algorithm 2 is lower bounded by `γ_K · UB_R[K] · T − O(N)`, where
`γ_K = max_{a ∈ ℤ₊} a/(a+1) · K/(K+a)`.

**Formalization Note.**
* `O(N)` is read as `C · N · Rmax` for one absolute constant `C`, chosen before the instance
  (the proof, p.ec6, loses at most `2 R_i(d_i) ≤ 2 Rmax` per selected arm, so `C = 2` works).
* "The schedule returned by Algorithm 2" is every output of every run (`IsAlg2Run`): any optimal
  `x*` with the property of Lemma 2, any maximizer `a*`, any admissible grouping, offsets and
  top-`K` selection. A run exists (first clause), and its output is a feasible `K`-PPP.
* `K ≤ N` (assumed in §2) is not needed; `K ≥ 1`.
* The reward is the sum of mean rewards (the objective of (1)); the first pull of each arm is
  measured from time `0`. -/
theorem theorem_1 :
    ∃ C : ℝ, ∀ (N K : ℕ) (R : Fin N → ℕ → ℝ) (Rmax : ℝ), 1 ≤ K → Admissible R Rmax →
      (∃ π : PPP N, IsAlg2Run R K π) ∧
      ∀ π : PPP N, IsAlg2Run R K π →
        IsKPPP K π ∧
        ∀ T : ℕ, 1 ≤ T →
          gamma K * UB R K * (T : ℝ) - C * (N : ℝ) * Rmax ≤ totalReward R π T := by sorry

end RecoveringBandits
