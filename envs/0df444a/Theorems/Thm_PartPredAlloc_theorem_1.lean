-- Prove2me | Theorems.Thm_PartPredAlloc_theorem_1
-- name    : PartPredAlloc.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:37.382206+00:00
-- url     : https://prove2.me/theorems/2636544b-6a05-44cb-80c6-71d343aa0ca8
-- title:
--   Theorem 1, p.15 — Algorithm 1 is $p+\frac{1-p}{2-a}-O\big(\frac1{a(1-p)p}\sqrt{\frac{\log n}b}\big)$ competitive
-- statement:
--   Consider the partially predictable model with $n\ge3$ periods, $b$ units of inventory, $1\le b\le n$, type-2 revenue $a\in(0,1)$ and $p\in(0,1)$. There is a constant $K$, independent of $n,b,a,p$ and of the instance, such that for every adversarial sequence $\vec v_I\in\{0,a,1\}^n$
--
--   $$
--   \mathbb E\big[ALG_1(\vec V)\big]\ \ge\ \Big(p+\frac{1-p}{2-a}-K\,\frac1{a(1-p)p}\sqrt{\frac{\log n}b}\Big)\,OPT(\vec v_I),
--   $$
--
--   where the expectation is over the stochastic group $\mathcal S$ and the uniform permutation $\sigma_{\mathcal S}$, and $\vec V=\vec v_I\circ\sigma^{-1}$ is the arrival sequence. In the words of the paper: for $p\in(0,1)$, the competitive ratio of Algorithm 1 is at least $p+\frac{1-p}{2-a}-O\big(\frac1{a(1-p)p}\sqrt{\frac{\log n}b}\big)$.
--
--   The main term $p+\frac{1-p}{2-a}$ interpolates between the random-order model ($p=1$) and the adversarial two-fare bound of Ball and Queyranne ($p=0$), and is tight by Remark 1.
--
--   Differences from the source:
--   - encoding: competitive ratio at least c − O(g) (Definitions 1, 2: E[ALG(V)] ≥ c·OPT(v_I); ∃ k, f(x) < k g(x) for all x) → ∃ K before n, b, a, p, v_I with (c − K·g)·OPT(v_I) ≤ E[ALG₁(V)]; reason: the non-strict form with ∃ K is equivalent to the strict one (replace K by K + 1, using OPT ≥ 0 and g > 0 for n ≥ 3)
--   - encoding: b units (b ≥ 0 implicit) → 1 ≤ b; reason: b = 0 makes log n / b undefined; the paper's b units and the error term presuppose b ≥ 1
--   - encoding: expectation over S, σ_S → expect n p: explicit finite sum with weights p^{|S|}(1−p)^{n−|S|} and σ uniform over the permutations fixing every position outside S; reason: the model has finitely many outcomes; this is its law (§3, p.10); Algorithm 1 is deterministic
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Theorem 1, p.15; Definition 1, p.10; Definition 2, p.12

import Mathlib
import Definitions.Def_PartPredAlloc_OPT
import Definitions.Def_PartPredAlloc_expect
import Definitions.Def_PartPredAlloc_alg1

namespace PartPredAlloc

/-- **Theorem 1** (Hwang–Jaillet–Manshadi, *Online Resource Allocation under Partially Predictable
Demand*, arXiv:1810.00447v1, Theorem 1, p.15). For `p ∈ (0, 1)`, the competitive ratio of
Algorithm 1 is at least `p + (1 − p)/(2 − a) − O((1/(a(1 − p)p)) √(log n / b))` in the partially
predictable model.

**Formalization Note.** Competitive ratio (Definition 1, p.10): `E[ALG(V)] ≥ c · OPT(v_I)` for
every adversarial instance `v_I`, the expectation over the stochastic group `S` (each position
independently with probability `p`) and the uniform permutation `σ` of `S` (`expect`), with
`V = v_I ∘ σ⁻¹`. `O(·)` (Definition 2, p.12): one constant `K`, chosen before `n, b, a, p` and
`v_I`; the non-strict form with `∃ K` is equivalent to the strict one (replace `K` by `K + 1`).
Model (§3, p.9): `n ≥ 3` periods, `1 ≤ b ≤ n` units, type-2 revenue `a ∈ (0, 1)`. `log` is the
natural logarithm. -/
theorem theorem_1 :
    ∃ K : ℝ, ∀ (n b : ℕ) (a p : ℝ), 3 ≤ n → 1 ≤ b → b ≤ n → 0 < a → a < 1 → 0 < p → p < 1 →
      ∀ vI : Fin n → Cust,
        (p + (1 - p) / (2 - a) - K * (1 / (a * (1 - p) * p)) * Real.sqrt (Real.log n / b)) *
            OPT b a vI ≤
          expect n p (fun _ σ => alg1 n b a p (arrival vI σ)) := by sorry

end PartPredAlloc
