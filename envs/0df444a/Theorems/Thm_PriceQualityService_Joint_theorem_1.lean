-- Prove2me | Theorems.Thm_PriceQualityService_Joint_theorem_1
-- name    : PriceQualityService.Joint.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:27.296982+00:00
-- url     : https://prove2.me/theorems/6be14270-caca-4201-87a6-4ca0907e2d42
-- title:
--   Theorem 1: optimal durations are extreme, qualities are $(\alpha_i+t_i^*b_i)/(2c_i)$, markups equal $1+r^*$, and $r^*$ is the optimal profit
-- statement:
--   Consider the joint optimization problem (4): choose prices $\mathbf p\in\mathbb R^N$, quality levels $\mathbf q\in\mathbb R^N$ and service durations $\mathbf t\in[t_s,t_l]^N$ to maximize the MNL profit
--   $$
--   \Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)=\sum_{i\in\mathcal N}\bigl[p_i-c_iq_i^2-t_i(a_i-b_iq_i)\bigr]\cdot\frac{\exp(\alpha_iq_i-p_i+t_is_i)}{1+\sum_{j\in\mathcal N}\exp(\alpha_jq_j-p_j+t_js_j)}.
--   $$
--   Assume $c_i>0$ for every $i$ and $t_s\le t_l$. Then:
--
--   1. **Existence and structure.** There are durations $\mathbf t^*$ with $t_i^*\in\{t_s,t_l\}$ for every $i$ (part (a)) and a real number $r^*$ that is the unique solution of
--   $$
--   r=\sum_{i\in\mathcal N}\exp\Bigl(\frac{b_i^2t_i^{*2}}{4c_i}+\Bigl(s_i-a_i+\frac{\alpha_ib_i}{2c_i}\Bigr)t_i^*+\frac{\alpha_i^2}{4c_i}-r-1\Bigr),
--   $$
--   such that with
--   $$
--   q_i^*=\frac{\alpha_i+t_i^*b_i}{2c_i},\qquad p_i^*=1+r^*+c_iq_i^{*2}+t_i^*(a_i-b_iq_i^*)
--   $$
--   (parts (b) and (c)) the triple $(\mathbf p^*,\mathbf q^*,\mathbf t^*)$ is optimal for (4) and its profit equals $r^*$.
--   2. **Every optimum has this structure.** If $(\mathbf p,\mathbf q,\mathbf t)$ is optimal for (4) with optimal profit $r^*=\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)$, then for every $i$: $q_i=(\alpha_i+t_ib_i)/(2c_i)$, $p_i=1+r^*+c_iq_i^2+t_i(a_i-b_iq_i)$, $r^*$ solves the equation above with $\mathbf t$ in place of $\mathbf t^*$, and, when $t_s<t_l$, $t_i\in\{t_s,t_l\}$ for every product with $b_i\ne0$ or $a_i\ne s_i$.
--
--   Thus the optimal service durations are extreme, each quality is set from the product's own parameters, all products carry the same markup $1+r^*$, and $r^*$ is the optimal profit.
--
--   **Formalization Note** $c_i>0$ is the paper's increasing convex production cost (p. 8). Qualities range over all of $\mathbb R$, as in the paper's proof; the model's range $[0,a_i/b_i)$ (p. 8) is not imposed. The paper's "always at a boundary point" is stated for optimal solutions in the precise form: when $b_i=0$ and $a_i=s_i$ the profit does not depend on $t_i$ once $q_i$ and $p_i$ are optimal, so every duration of product $i$ is optimal; for all other products every optimal duration is $t_s$ or $t_l$ (this needs $t_s<t_l$; when $t_s=t_l$ the claim is trivial). Products are `Fin N` (0-based) and $N=0$ is allowed (then $r^*=0$).
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), pp. 9–10, Theorem 1; proof pp. 25–27, Appendix B

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Joint

/-- Theorem 1, Wang, Ke & Cui, pp. 9–10, for problem (4): maximize the profit (3) over prices
`p ∈ ℝ^N`, qualities `q ∈ ℝ^N` and service durations `t ∈ [t_s, t_l]^N`.

First conjunct (existence, (a)–(c)): there are durations `t*` with every `t*_i ∈ {t_s, t_l}` and a
real `r*` that is the unique root of
`r = ∑_i exp(b_i² t*_i²/(4c_i) + (s_i − a_i + α_i b_i/(2c_i)) t*_i + α_i²/(4c_i) − r − 1)`, such that
with `q*_i = (α_i + t*_i b_i)/(2c_i)` and `p*_i = 1 + r* + c_i q*_i² + t*_i(a_i − b_i q*_i)` the triple
`(p*, q*, t*)` is optimal and its profit is `r*`.

Second conjunct (every optimum has this structure): if `(p, q, t)` is optimal with value
`r* = Π(p, q, t)`, then `q_i = (α_i + t_i b_i)/(2c_i)`, `p_i = 1 + r* + c_i q_i² + t_i(a_i − b_i q_i)`,
`r*` solves the equation above at `t`, and, when `t_s < t_l`, `t_i ∈ {t_s, t_l}` for every `i` with
`b_i ≠ 0` or `a_i ≠ s_i` (when `b_i = 0` and `a_i = s_i` every duration of product `i` is optimal). -/
theorem theorem_1 {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (hst : ts ≤ tl) :
    (∃ (tstar : Fin N → ℝ) (rstar : ℝ),
      (∀ i, tstar i = ts ∨ tstar i = tl) ∧
      rstar = ∑ i, Real.exp (durationExponent α a b c s i (tstar i) - rstar - 1) ∧
      (∀ r : ℝ, r = ∑ i, Real.exp (durationExponent α a b c s i (tstar i) - r - 1) → r = rstar) ∧
      (let qstar : Fin N → ℝ := fun i => (α i + tstar i * b i) / (2 * c i)
       let pstar : Fin N → ℝ := fun i =>
         1 + rstar + c i * qstar i ^ 2 + tstar i * (a i - b i * qstar i)
       (∀ p q t : Fin N → ℝ, (∀ i, t i ∈ Set.Icc ts tl) →
          profit α a b c s p q t ≤ profit α a b c s pstar qstar tstar) ∧
        profit α a b c s pstar qstar tstar = rstar)) ∧
    (∀ p q t : Fin N → ℝ, (∀ i, t i ∈ Set.Icc ts tl) →
      (∀ p' q' t' : Fin N → ℝ, (∀ i, t' i ∈ Set.Icc ts tl) →
          profit α a b c s p' q' t' ≤ profit α a b c s p q t) →
      (∀ i, q i = (α i + t i * b i) / (2 * c i)) ∧
      (∀ i, p i = 1 + profit α a b c s p q t + c i * q i ^ 2 + t i * (a i - b i * q i)) ∧
      profit α a b c s p q t =
        ∑ i, Real.exp (durationExponent α a b c s i (t i) - profit α a b c s p q t - 1) ∧
      (ts < tl → ∀ i, (b i ≠ 0 ∨ a i ≠ s i) → t i = ts ∨ t i = tl)) := by sorry

end PriceQualityService.Joint
