-- Prove2me | Theorems.Thm_SinglePointPricing_Det_propD1_worst_terms
-- name    : SinglePointPricing.Det.propD1_worst_terms
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T09:30:44.287461+00:00
-- url     : https://prove2.me/theorems/c617306e-6550-470a-a9bb-defcfe9153c8
-- title:
--   Proof of Proposition D-1, (D-4)–(D-5), pp. App-17–20 — the first and third worst-case terms against a deterministic price
-- statement:
--   Fix $\alpha\in[0,1]$ and $q\in(0,1)$, normalize the historical price to $w=1$, and write $\underline r=\underline r_\alpha(1,q)=1/(\Gamma_\alpha^{-1}(q)+1)$. These are the two worst-case computations inside the proof of Proposition D-1.
--
--   **First term (D-5).** For every normalized price $p\in(\underline r,1)$, the infimum
--   $$\inf_{r\in[\underline r,\,p)}\ \frac{p\,\overline F_\alpha(p\mid r,(1,q))}{r}$$
--   is attained (at $r=\mu_{\alpha,q}(p)\in[\underline r,p)$) and equals $R_{1,\alpha}(p,q)=\dfrac{p\,\overline F_\alpha(p\mid \mu_{\alpha,q}(p),(1,q))}{\mathrm{opt}(F_\alpha(\cdot\mid \mu_{\alpha,q}(p),(1,q)))}$.
--
--   **Third term (D-4).** If $q\ge \underline q_\alpha$, then for every $p\in[0,1]$
--   $$\inf_{r\in[1,\,\overline r_\alpha(1,q)]}\ \frac{p\,\overline F_\alpha(p\mid r,(1,q))}{\mathrm{opt}(F_\alpha(\cdot\mid r,(1,q)))} = R_{3,\alpha}(p,q),$$
--   where $r\le\overline r_\alpha(1,q)=1/(\alpha\Gamma_\alpha^{-1}(q))$ is written as $\alpha\Gamma_\alpha^{-1}(q)\,r\le1$ (no upper constraint for $\alpha=0$). For $\alpha>0$ the infimum is attained at $\overline r_\alpha(1,q)$; for $\alpha=0$ it is the limit $r\to\infty$, matching the encoding of $R_{3,0}$.
--
--   Together with the identity term $p$ (the point mass at $1$), these give the three worst cases faced by a deterministic price, and they are exactly what is needed to evaluate the worst-case ratio of a given price, as in the proof of Theorem 2.
--
--   Differences from the source:
--   - reading: 'for any p in [0,1]' in (D-5) → p ∈ (r̲_α(1,q), 1); reason: for p ≤ r̲_α(1,q) the index set [r̲_α(1,q), p) is empty (the term imposes no constraint), and at p = 1 the law F_α(·|µ_{α,q}(1),(1,q)) falls in the r ≥ w branch of (3.2); the proof (App-19) establishes µ_{α,q}(p) ∈ [r̲_α(1,q), p) using p ≥ r̲_α(1,q)
--   - encoding: the infimum of (D-5) stated as IsLeast (attained at µ_{α,q}(p)), and the infimum of (D-4) stated as IsGLB (attained at r̄_α(1,q) when α > 0, a limit when α = 0, r̄_0 = +∞)
--   - encoding: opt(F_α(·|r,(1,q))) for r < 1 replaced by r in (D-5), as printed (Lemma C-2: r is an optimal price of F_α(·|r,(1,q))); in (D-4) opt is computed from the ccdf (3.2) as sup_{v ≥ 0} v F̄_α(v|r,(1,q))
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Appendix D.1, proof of Proposition D-1, displays (D-4) and (D-5), pp. App-17–20

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det

/-- Proof of Proposition D-1, displays (D-4) and (D-5), pp. App-17–20 (initial price normalized to
`w = 1`). First term (D-5): for every normalized price `p ∈ (r̲_α(1,q), 1)`, the infimum over
`r ∈ [r̲_α(1,q), p)` of `p F̄_α(p|r,(1,q))/r` is attained (at `r = µ_{α,q}(p)`) and equals
`R_{1,α}(p,q)`. Third term (D-4): if `q ≥ q̲_α`, then for every `p ∈ [0, 1]` the infimum over
`r ∈ [1, r̄_α(1,q)]` of `p F̄_α(p|r,(1,q))/opt(F_α(·|r,(1,q)))` equals `R_{3,α}(p,q)`. -/
theorem propD1_worst_terms (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (q : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ p ∈ Set.Ioo (rLow α 1 q) 1,
      IsLeast ((fun r => p * Fbar α 1 q r p / r) '' Set.Ico (rLow α 1 q) p) (R1 α q p)) ∧
    (qLow α ≤ q → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      IsGLB ((fun r => p * Fbar α 1 q r p / optFun (Fbar α 1 q r)) ''
        {r | 1 ≤ r ∧ α * GammaAInv α q * r ≤ 1}) (R3 α q p)) := by sorry

end SinglePointPricing.Det
