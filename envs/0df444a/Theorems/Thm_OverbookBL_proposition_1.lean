-- Prove2me | Theorems.Thm_OverbookBL_proposition_1
-- name    : OverbookBL.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:50:37.829022+00:00
-- url     : https://prove2.me/theorems/751381ac-3d19-4805-9bca-23be4d76ae98
-- title:
--   Proposition 1 — Berry–Esseen for independent non-identical summands, constant $6$ (Feller XVI.5)
-- statement:
--   Let $J_1,\dots,J_m$ be independent real random variables with $\mathbb E[J_r]=0$, $\mathbb E[J_r^2]=\sigma_r^2$ and $\mathbb E[|J_r|^3]=\kappa_r<\infty$. Put
--
--   $$
--   s_m^2=\sum_{r=1}^m\sigma_r^2,\qquad g_m=\sum_{r=1}^m\kappa_r,
--   $$
--
--   assume $s_m>0$, and let $J'=(J_1+\dots+J_m)/s_m$. Then for all $x\in\mathbb R$,
--
--   $$
--   \big|F_{J'}(x)-\Phi(x)\big|\le\frac{6\,g_m}{s_m^3},
--   $$
--
--   where $F_{J'}$ is the distribution function of $J'$ and $\Phi$ that of the standard normal law.
--
--   The paper applies it to centred Bernoulli sums to locate the quantiles of a Poisson binomial law (Claim 1).
--
--   Differences from the source:
--   - encoding: independent random variables with the stated moments → measurable functions on a probability space, iIndepFun, MemLp 3 (finite third moments), and s_m > 0; reason: measurability makes the law of J′ a probability measure; finite moments and s_m > 0 make every quantity in (6) defined
--   - encoding: E[|J³_r|] → E|J_r|³; reason: the same number
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Proposition 1, Appendix A.2, p.40 (Theorem 2 of Chapter XVI.5 in Feller)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace OverbookBL

/-- **Proposition 1** (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2,
Appendix A.2, p.40; Theorem 2 of Chapter XVI.5 in Feller, *An Introduction to Probability Theory
and Its Applications*). Let `J₁, …, Jₘ` be independent real random variables with `E[Jᵣ] = 0`,
`E[Jᵣ²] = σᵣ²` and `E[|Jᵣ|³] = κᵣ`. Put `sₘ² = ∑ σᵣ²`, `gₘ = ∑ κᵣ`, and let `J′` be the normalized
sum `(J₁ + ⋯ + Jₘ)/sₘ`. Then for all `x`,
`|F_{J′}(x) − Φ(x)| ≤ 6 gₘ / sₘ³`,
where `Φ` is the standard normal distribution function.

**Formalization Note** The variables live on an arbitrary probability space and are measurable
(so that the law of `J′` is a probability measure); finite third moments (`MemLp _ 3`) make every
moment in the statement finite, and `sₘ > 0` makes the normalization defined. The printed
`E[|J³ᵣ|]` is `E|Jᵣ|³`. `F_{J′}` is `cdf` of the law of `J′` and `Φ` is `cdf (gaussianReal 0 1)`. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ) (J : Fin m → Ω → ℝ) (hmeas : ∀ r, Measurable (J r)) (hind : iIndepFun J P) (hmom : ∀ r, MemLp (J r) 3 P) (hmean : ∀ r, ∫ ω, J r ω ∂P = 0) (hs : 0 < ∑ r, ∫ ω, J r ω ^ 2 ∂P) (x : ℝ) : |cdf (P.map (fun ω => (∑ r, J r ω) / Real.sqrt (∑ r, ∫ ω, J r ω ^ 2 ∂P))) x - cdf (gaussianReal 0 1) x| ≤ 6 * (∑ r, ∫ ω, |J r ω| ^ 3 ∂P) / Real.sqrt (∑ r, ∫ ω, J r ω ^ 2 ∂P) ^ 3 := by sorry

end OverbookBL
