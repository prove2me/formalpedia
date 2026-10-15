-- Prove2me | Theorems.Thm_RefMNLPricing_MultiVsSingle_remark_4_identical
-- name    : RefMNLPricing.MultiVsSingle.remark_4_identical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T11:43:10.066325+00:00
-- url     : https://prove2.me/theorems/5d980b59-c19d-4df5-9fa5-54669fbc9f4f
-- title:
--   Remark 4, p. 27 — for identical products q_i(p⋆⋆, p⋆⋆) < 1/n, and (26b) implies (28)
-- statement:
--   Consider $n\ge2$ products with identical parameters $a$, $b>0$ and loss-neutral sensitivity $c\ge0$, with $\alpha\in[0,1]$, $\beta\in[0,1)$ and $\kappa=(1-\beta)/(1-\alpha\beta)$. Let $\Pi^{\star\star}$ solve (24) for these parameters, i.e. $\Pi^{\star\star}=\frac{n}{b+c\kappa}\exp\big(a-b\Pi^{\star\star}-\frac{b}{b+c\kappa}\big)$, and let $p^{\star\star}=\Pi^{\star\star}+1/(b+c\kappa)$. Then
--
--   1. every market share at the uniform vector $p^{\star\star}\mathbf 1$ is below $1/n$: $q_i(p^{\star\star}\mathbf 1,p^{\star\star}\mathbf 1)<1/n$ for all $i$;
--   2. if
--   $$
--   \big[(1-\kappa)^2+\beta(1-\alpha\kappa)^2\big]c^2-(1+\beta\alpha^2)(b+c\kappa)^2\ \ge\ \frac{(b+c)^2+\beta(\alpha b+c)^2}{n-1},\qquad(26b)
--   $$
--   then condition (28) of Remark 4 holds for some product $i$.
--
--   These are the two follow-up sentences of Remark 4 that connect it to Theorem 7.
--
--   **Formalization Note.** The paper says it is "straightforward to derive Eq. (26b) from Eq. (28)"; since (26b) is the sufficient condition of Theorem 7, the statement formalizes the implication (26b) ⇒ (28) needed for that role. The hypothesis $n\ge2$ makes $n-1>0$ in (26b).
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 27, Remark 4 (last three sentences), with (26b) from p. 25

import Mathlib
import Definitions.Def_RefMNLPricing_MultiVsSingle_Model

namespace RefMNLPricing.MultiVsSingle

/-- Remark 4, p. 27, the identical-products sentences: for `n ≥ 2` products with identical
loss-neutral parameters `a, b, c`, every product's market share at the candidate `p⋆⋆ = p⋆⋆ · 1`
(`p⋆⋆ = Π⋆⋆ + 1/(b + cκ)`, `Π⋆⋆` solving (24)) is below `1/n`, and (26b) implies (28). -/
theorem remark_4_identical {n : ℕ} (a b c α β : ℝ)
    (hn : 2 ≤ n) (hb : 0 < b) (hc : 0 ≤ c)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (Rss : ℝ)
    (hRss : Rss = n / (b + c * RefMNLPricing.SteadyState.kappa α β) *
      Real.exp (a - b * Rss - b / (b + c * RefMNLPricing.SteadyState.kappa α β))) :
    (∀ i : Fin n, RefMNLPricing.Myopic.share (fun _ => a) (fun _ => b) (fun _ => c) (fun _ => c)
        (fun _ => Rss + 1 / (b + c * RefMNLPricing.SteadyState.kappa α β)) (fun _ => Rss + 1 / (b + c * RefMNLPricing.SteadyState.kappa α β)) i
        < 1 / n) ∧
    (((1 - RefMNLPricing.SteadyState.kappa α β) ^ 2 + β * (1 - α * RefMNLPricing.SteadyState.kappa α β) ^ 2) * c ^ 2
        - (1 + β * α ^ 2) * (b + c * RefMNLPricing.SteadyState.kappa α β) ^ 2 ≥
        ((b + c) ^ 2 + β * (α * b + c) ^ 2) / ((n : ℝ) - 1) →
      ∃ i : Fin n, kappa1 (fun _ => b) (fun _ => c) α β i - kappa2 (fun _ => b) (fun _ => c) α β i >
        (2 * kappa1 (fun _ => b) (fun _ => c) α β i - kappa2 (fun _ => b) (fun _ => c) α β i) *
          RefMNLPricing.Myopic.share (fun _ => a) (fun _ => b) (fun _ => c) (fun _ => c)
            (fun _ => Rss + 1 / (b + c * RefMNLPricing.SteadyState.kappa α β))
            (fun _ => Rss + 1 / (b + c * RefMNLPricing.SteadyState.kappa α β)) i) := by sorry

end RefMNLPricing.MultiVsSingle
