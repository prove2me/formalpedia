-- Prove2me | Theorems.Thm_OrdinalMSP_Forbidden_conditional_product_bound
-- name    : OrdinalMSP.Forbidden.conditional_product_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:33.869002+00:00
-- url     : https://prove2.me/theorems/d801132a-0099-4f0c-966d-5c28ac9fb5a9
-- title:
--   Proof of Lemma 1, p. 9 — conditioned on s, r_t = r* and R_t = Y, Pr(r* ∈ ALG) ≥ ∏_{j=s+1}^{t−1} ((j−k)/j)_+
-- statement:
--   Let $\mathcal M$ be a matroid on $R$ with $|R| = n$ and value order $\succ$, and let $\mathrm{ALG}$ be an algorithm with forbidden sets of size $k$ (Definition 7). Fix $r^* \in \mathrm{OPT}$, a sample size $s$, a time $t$ with $s + 1 \le t \le n$, and a set $Y \subseteq R$ with $|Y| = t$ and $r^* \in Y$. Condition on the event that $r^*$ arrives at time $t$ and that the first $t$ arrivals form $Y$, i.e. $r_t = r^*$ and $R_t = Y$, the arrival order being uniform. Writing $\mathbb P_t(\cdot) = \Pr(\cdot \mid r_t = r^*, R_t = Y, s)$, we have
--   $$\mathbb P_t(r^* \in \mathrm{ALG}) \ \ge\ \prod_{j=s+1}^{t-1} \left(\frac{j-k}{j}\right)_+, \qquad x_+ = \max\{0, x\}.$$
--
--   This is the per-scenario bound of the Key Lemma: going backwards from time $t-1$ to $s+1$, each arrival $r_j$ is a uniform element of $R_j$ and avoids the at most $k$ forbidden elements of $R_j$ with probability at least $(j-k)/j$.
--
--   **Formalization Note** The conditional probability is the ratio of two counts over the $n!$ arrival orders, and the statement is written multiplicatively to avoid a zero denominator: with $C = \{\sigma : r^* \text{ arrives at time } t,\ R_t = Y\}$,
--   $$\prod_{j=s+1}^{t-1} \max\Bigl\{0, \frac{j-k}{j}\Bigr\} \cdot |C| \ \le\ \bigl|\{\sigma \in C : r^* \in \mathrm{ALG}(\sigma, s)\}\bigr|.$$
--   Times are 1-based as on the page ($j$ ranges over `Finset.Ico (s+1) t`); "$r^*$ arrives at time $t$" is `σ.symm r = t - 1` for the 0-based arrival index. The middle equality of the paper's display (the probability as a product of step probabilities) is not stated; only the outer inequality is.
-- source:
--   Soto, Turkieltaub & Verdugo, Strong Algorithms for the Ordinal Matroid Secretary Problem, arXiv:1802.01997v1, proof of Lemma 1, p. 9, first display ("ℙ_t(r∗ ∈ ALG) ≥ … ≥ ∏_{j=s+1}^{t−1} ((j − k)/j)_+")

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting

namespace OrdinalMSP.Forbidden

theorem conditional_product_bound {R : Type*} [Fintype R] [DecidableEq R] [LinearOrder R]
    (M : Matroid R) (hE : M.E = Set.univ) (k : ℕ) (ALG : ArrivalOrder R → ℕ → Finset R)
    (hALG : HasForbiddenSets M k ALG) (r : R) (hr : r ∈ opt M Finset.univ)
    (s t : ℕ) (hst : s + 1 ≤ t) (htn : t ≤ Fintype.card R)
    (Y : Finset R) (hY : Y.card = t) (hrY : r ∈ Y) :
    (∏ j ∈ Finset.Ico (s + 1) t, max 0 (((j : ℝ) - (k : ℝ)) / (j : ℝ))) *
        ((Finset.univ.filter (fun σ : ArrivalOrder R =>
            ((σ.symm r : ℕ) = t - 1 ∧ arrived σ t = Y))).card : ℝ) ≤
      ((Finset.univ.filter (fun σ : ArrivalOrder R =>
            ((σ.symm r : ℕ) = t - 1 ∧ arrived σ t = Y) ∧ r ∈ ALG σ s)).card : ℝ) := by sorry

end OrdinalMSP.Forbidden
