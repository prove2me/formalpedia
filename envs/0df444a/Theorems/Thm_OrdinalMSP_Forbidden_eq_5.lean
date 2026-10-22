-- Prove2me | Theorems.Thm_OrdinalMSP_Forbidden_eq_5
-- name    : OrdinalMSP.Forbidden.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:34.68799+00:00
-- url     : https://prove2.me/theorems/2e937572-781f-4daf-a159-15a368fbc6ed
-- title:
--   (5), p. 9 — Pr(r* ∈ ALG) ≥ E_{s∼Bin(n,p)} (1/n) Σ_{t=s+1}^{n} ∏_{j=s+1}^{t−1} (1 − k/j)_+
-- statement:
--   Let $\mathcal M$ be a matroid on $R$ with $|R| = n$ and value order $\succ$, and let $\mathrm{ALG}$ be an algorithm with forbidden sets of size $k$ (Definition 7). Let the sampling probability satisfy $0 \le p \le 1$, so that the sample size is $s \sim \mathrm{Bin}(n, p)$, drawn independently of a uniformly random arrival order. Then for every $r^* \in \mathrm{OPT}$,
--   $$\Pr(r^* \in \mathrm{ALG}) \ \ge\ \mathbb E_{s \sim \mathrm{Bin}(n,p)}\, \frac1n \sum_{t=s+1}^{n} \prod_{j=s+1}^{t-1} \left(1 - \frac{k}{j}\right)_+ ,$$
--   where $x_+ = \max\{0, x\}$ and the expectation is $\sum_{s=0}^{n} \binom{n}{s} p^s (1-p)^{n-s}(\cdot)$.
--
--   This is display (5), obtained in the paper by removing the conditioning of the per-scenario bound: $r^*$ arrives at each time $t$ with probability $1/n$. The right-hand side no longer depends on the matroid or on the algorithm.
--
--   **Formalization Note** $\Pr(r^* \in \mathrm{ALG})$ is the finite-sum selection probability of the Setting definition. The sums and products are written out: $t$ ranges over `Finset.Icc (s+1) n` and $j$ over `Finset.Ico (s+1) t`, all 1-based times, and $1 - k/j$ is computed in $\mathbb R$. For $n = 0$ the ground set is empty and so is $\mathrm{OPT}$.
-- source:
--   Soto, Turkieltaub & Verdugo, Strong Algorithms for the Ordinal Matroid Secretary Problem, arXiv:1802.01997v1, proof of Lemma 1, display (5), p. 9

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting

namespace OrdinalMSP.Forbidden

theorem eq_5 {R : Type*} [Fintype R] [DecidableEq R] [LinearOrder R]
    (M : Matroid R) (hE : M.E = Set.univ) (k : ℕ) (ALG : ArrivalOrder R → ℕ → Finset R)
    (hALG : HasForbiddenSets M k ALG) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r : R) (hr : r ∈ opt M Finset.univ) :
    ∑ s ∈ Finset.range (Fintype.card R + 1),
        ((Fintype.card R).choose s : ℝ) * p ^ s * (1 - p) ^ (Fintype.card R - s) *
          ((1 / (Fintype.card R : ℝ)) *
            ∑ t ∈ Finset.Icc (s + 1) (Fintype.card R),
              ∏ j ∈ Finset.Ico (s + 1) t, max 0 (1 - (k : ℝ) / (j : ℝ)))
      ≤ selProb ALG p r := by sorry

end OrdinalMSP.Forbidden
