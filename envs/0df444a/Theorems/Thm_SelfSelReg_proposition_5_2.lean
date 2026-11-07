-- Prove2me | Theorems.Thm_SelfSelReg_proposition_5_2
-- name    : SelfSelReg.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:31.330044+00:00
-- url     : https://prove2.me/theorems/b7a946e5-292f-4a04-9eef-d74f0f9873f1
-- title:
--   Proposition 5.2 — conditional Hermite identity $\mathbb E[H_d(G)\mid Y=t]=\frac{\mathrm{He}_d(t/\sigma)}{\sigma^d\sqrt{d!}}v^{\otimes d}$
-- statement:
--   Let $G\in\mathbb R^n$ and $Y\in\mathbb R$ be centered jointly Gaussian, with $G\sim N(0,I_n)$ and $\mathrm{Var}(Y)=\sigma^2>0$, and put $v=\mathbb E[GY]$. Let $H_d$ be the normalized Hermite tensor of order $d$ and $\mathrm{He}_d$ the probabilists' Hermite polynomial. Then for every integer $d\ge0$ and every $t\in\mathbb R$,
--   $$\mathbb E\big[H_d(G)\mid Y=t\big]=\frac{\mathrm{He}_d(t/\sigma)}{\sigma^d\sqrt{d!}}\,v^{\otimes d}.$$
--
--   Conditioning on a Gaussian linear functional thus turns the Hermite tensor into a scalar Hermite polynomial times a rank-one tensor. Integrated over a slice of $Y$, this gives the single-response moment identity (Corollary 5.3), the source of the rank-one terms in the moment structure theorem.
--
--   **Formalization Note** The conditional expectation is the integral against the explicit conditional law of Proposition 4.3 (`gaussCondLaw`), for every $t$; the identity is stated entrywise.
--
--   Differences from the source:
--   - encoding: a centered jointly Gaussian pair (G, Y) with G ∼ N(0, I_n), Var(Y) = σ² > 0, v = E[GY] → parameters v and σ² with 0 < σ², ‖v‖² ≤ σ², and the law of (G, ⟨v, G⟩ + √(σ² − ‖v‖²)·g), g ∼ N(0, 1) independent; reason: every such pair has this law (‖v‖² ≤ σ² is forced), and the statement depends only on the law
--   - encoding: E[· | Y = t] for every t → the integral against the explicit conditional law gaussCondLaw n v σ² t of Proposition 4.3; reason: the conditioning event is null; this is the continuous version of the conditional law that the proofs compute, defined for every t, instead of an almost-everywhere defined conditional expectation evaluated at a point
--   - encoding: an identity of order-d tensors → an identity of every entry, indexed by J : Fin d → Fin n; reason: tensors are functions of index tuples; same content
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Proposition 5.2, p.20 (PDF p.23); proof Appendix C.2

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_SelfSelReg_Tensor
import Definitions.Def_SelfSelReg_gaussCondLaw

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Proposition 5.2** (Conditional Hermite Identity).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Proposition 5.2, p.20 (PDF p.23): "Let G ∈ ℝⁿ and Y ∈ ℝ be centered
jointly Gaussian, with G ∼ N(0, I_n) and Var(Y) = σ² > 0. Put v = E_{G,Y}[GY]. For every integer
d ≥ 0 and t ∈ ℝ, E_{G,Y}[H_d(G) | Y = t] = He_d(t/σ)/(σ^d √d!) · v^{⊗d}."

**Formalization Note.** The pair is parametrized by `v = E[GY]` and `σ² = Var(Y)` with
`‖v‖² ≤ σ²`, which determine its law; `E[· | Y = t]` is the integral against the explicit conditional
law `gaussCondLaw n v σ² t` of Proposition 4.3. The identity is entrywise in the order-`d` tensor;
`He_d(t/σ)/√d!` is `GaussPart.hermiteOne d (t/σ)`. Each entry of `H_d` is a polynomial, integrable
under the Gaussian conditional law. -/
theorem proposition_5_2 (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (σsq : ℝ) (hσ : 0 < σsq)
    (hv : ‖v‖ ^ 2 ≤ σsq) (d : ℕ) (t : ℝ) (J : Fin d → Fin n) :
    ∫ z, GaussPart.hermiteTensor d z.1 J ∂(gaussCondLaw n v σsq t) =
      GaussPart.hermiteOne d (t / Real.sqrt σsq) / Real.sqrt σsq ^ d * tensorPow v d J := by sorry

end SelfSelReg
