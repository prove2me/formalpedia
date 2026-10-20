-- Prove2me | Theorems.Thm_SellingData_ListsBinary_proposition2_lists_distortion
-- name    : SellingData.ListsBinary.proposition2_lists_distortion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:49.352751+00:00
-- url     : https://prove2.me/theorems/7aa614c0-619e-4838-bf9b-dc1df5abc39f
-- title:
--   Proposition 2, p. 11 — marketing lists: α*_L = α^e_L; α*_H > α^e_H if φ < 1/2 and α*_H < α^e_H if φ > 1/2
-- statement:
--   Consider the screening problem (6) of *Selling Data to Marketers* for marketing lists: a data seller offers a menu $(T_H,\alpha_H),(T_L,\alpha_L)$ to marketers whose targeting cost is $c_H$ with probability $\theta$ and $c_L<c_H$ with probability $1-\theta$, subject to $T_j\ge0$, $\alpha_j\in[\underline\alpha,\bar\alpha]$, individual rationality and incentive compatibility, and maximizes $\Pi=\theta[T_H-k(\alpha_H)]+(1-\theta)[T_L-k(\alpha_L)]$. Under the benchmark with observable cost, the efficient informativeness $\alpha^e_i$ for type $i$ maximizes $\theta_i\big[\sigma_h(\alpha)[v_h(\alpha)-c_i]-k(\alpha)\big]$ over $[\underline\alpha,\bar\alpha]$.
--
--   Assume, in addition to the model, that $k$ is continuous on $[\underline\alpha,\bar\alpha]$, differentiable on $(\underline\alpha,\bar\alpha)$, has right derivative $k'(\underline\alpha)=0$, and $k'(\alpha)\to+\infty$ as $\alpha\to\bar\alpha^-$. Then:
--   1. the low-cost plan is efficient: $a$ is the $\alpha_L$ of some optimal menu if and only if $a$ is efficient for type $L$, i.e. $\alpha^*_L=\alpha^e_L$;
--   2. if $\phi<1/2$, every optimal menu and every efficient $a$ for type $H$ satisfy $\alpha^*_H>a$;
--   3. if $\phi>1/2$, every optimal menu and every efficient $a$ for type $H$ satisfy $\alpha^*_H<a$.
--   $$\alpha^*_L=\alpha^e_L,\qquad \alpha^*_H>\alpha^e_H\ \text{if }\phi<1/2,\qquad \alpha^*_H<\alpha^e_H\ \text{if }\phi>1/2.$$
--
--   Unlike in standard screening, the information given to the low type (the high-cost marketers) may be distorted upward as well as downward, according to whether the information rent $\sigma_h(\alpha_H)(c_H-c_L)$ falls or rises with $\alpha_H$.
--
--   **Formalization Note** The regularity of $k$ is the part of footnote 5 (p. 7) that makes the benchmark optimum interior; without it an optimum can sit at a corner where $\alpha^*_H=\alpha^e_H$, and the strict inequalities fail. Convexity and twice differentiability, also listed in the footnote, are not assumed. Optimal menus are those of the full problem (6) with all four constraints and $T\ge0$, not maximizers of (7); "$\alpha^*_L=\alpha^e_L$" is equality of maximizer sets and the inequalities hold for every optimal menu against every efficient level, since neither need be unique.
-- source:
--   Guo, Selling Data to Marketers, author's manuscript (Management Science, doi:10.1287/mnsc.2023.01350), p. 11, Proposition 2 (proof p. 31); regularity of k from footnote 5, p. 7

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting

namespace SellingData.ListsBinary

/-- Proposition 2, p. 11: in selling marketing lists, the low-cost plan of an optimal menu is
efficient (`α*_L = α^e_L`, as equality of maximizer sets), and the high-cost plan carries
strictly more information than every efficient benchmark level if `φ < 1/2` and strictly less
if `φ > 1/2`. Regularity of `k` from footnote 5, p. 7: continuity on `[α̲, ᾱ]`,
differentiability inside, `k'(α̲) = 0` (one-sided), `k'(α) → +∞` as `α → ᾱ⁻`. -/
theorem proposition2_lists_distortion (S : Screening)
    (hk_cont : ContinuousOn S.k (Set.Icc S.aLo S.aHi))
    (hk_diff : ∀ a ∈ Set.Ioo S.aLo S.aHi, DifferentiableAt ℝ S.k a)
    (hk_left : HasDerivWithinAt S.k 0 (Set.Ici S.aLo) S.aLo)
    (hk_right : Filter.Tendsto (deriv S.k) (nhdsWithin S.aHi (Set.Iio S.aHi)) Filter.atTop) :
    (∀ a : ℝ, (∃ m : Menu, S.IsOptimalMenu m ∧ m.αL = a) ↔ S.IsEfficientType .L a) ∧
    (S.phi < 1 / 2 →
      ∀ m : Menu, S.IsOptimalMenu m → ∀ a : ℝ, S.IsEfficientType .H a → a < m.αH) ∧
    (1 / 2 < S.phi →
      ∀ m : Menu, S.IsOptimalMenu m → ∀ a : ℝ, S.IsEfficientType .H a → m.αH < a) := by sorry

end SellingData.ListsBinary
