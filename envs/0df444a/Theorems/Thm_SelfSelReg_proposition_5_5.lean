-- Prove2me | Theorems.Thm_SelfSelReg_proposition_5_5
-- name    : SelfSelReg.proposition_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:29.971271+00:00
-- url     : https://prove2.me/theorems/a3250933-1144-43b1-8389-be541a41ecfc
-- title:
--   Proposition 5.5 — conditional Hermite second moment bound
-- statement:
--   Let $G\in\mathbb R^n$ and $Y\in\mathbb R$ be centered jointly Gaussian, with $G\sim N(0,I_n)$ and $\mathrm{Var}(Y)=\sigma^2>0$, and put $v=\mathbb E[GY]$. For every integer $d\ge0$, every symmetric order-$d$ tensor $A$, every $t\in\mathbb R$ and every $0<\rho<1/2$,
--   $$\Big(\mathbb E\big[\langle H_d(G),A\rangle^2\mid Y=t\big]\Big)^{1/2}\le\frac{\rho^{-d/2}}{\sqrt{1-2\rho}}\exp\Big(\frac{\rho\|v\|_2^2t^2}{2\sigma^4(1-2\rho)}\Big)\|A\|_F .$$
--   Here $\langle\cdot,\cdot\rangle$ is the Frobenius inner product and $\|A\|_F$ the Frobenius norm.
--
--   This bound on the Hermite features conditioned on a large response is combined with Lemma 5.4 by Cauchy–Schwarz to bound the decomposition error in Theorem 5.1(i).
--
--   **Formalization Note** The conditional expectation is the integral against the explicit conditional law `gaussCondLaw` of Proposition 4.3; $\sigma^4=(\sigma^2)^2$.
--
--   Differences from the source:
--   - encoding: a centered jointly Gaussian pair (G, Y) with G ∼ N(0, I_n), Var(Y) = σ² > 0, v = E[GY] → parameters v and σ² with 0 < σ², ‖v‖² ≤ σ², and the law of (G, ⟨v, G⟩ + √(σ² − ‖v‖²)·g), g ∼ N(0, 1) independent; reason: every such pair has this law (‖v‖² ≤ σ² is forced), and the statement depends only on the law
--   - encoding: E[· | Y = t] for every t → the integral against the explicit conditional law gaussCondLaw n v σ² t of Proposition 4.3; reason: the conditioning event is null; this is the continuous version of the conditional law that the proofs compute, defined for every t, instead of an almost-everywhere defined conditional expectation evaluated at a point
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Proposition 5.5, p.21 (PDF p.24); proof Appendix C.3

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_SelfSelReg_Tensor
import Definitions.Def_SelfSelReg_gaussCondLaw

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Proposition 5.5** (Conditional Hermite Second Moment).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Proposition 5.5, p.21 (PDF p.24): "Let G ∈ ℝⁿ and Y ∈ ℝ be centered
jointly Gaussian, with G ∼ N(0, I_n) and Var(Y) = σ² > 0. Put v = E_{G,Y}[GY]. For every integer
d ≥ 0, symmetric order-d tensor A, t ∈ ℝ, and 0 < ρ < 1/2,
(E_{G,Y}[⟨H_d(G), A⟩² | Y = t])^{1/2} ≤ ρ^{−d/2}/√(1 − 2ρ) · exp(ρ‖v‖₂²t²/(2σ⁴(1 − 2ρ))) · ‖A‖_F."

**Formalization Note.** The pair is parametrized by `v` and `σ²` with `‖v‖² ≤ σ²`, and
`E[· | Y = t]` is the integral against `gaussCondLaw n v σ² t` (Proposition 4.3). `⟨·,·⟩` is the
Frobenius inner product `frobInner`, `‖A‖_F` is `GaussPart.frobeniusNorm`, and `σ⁴ = (σ²)²`. The
integrand is a polynomial, integrable under the Gaussian conditional law. -/
theorem proposition_5_5 (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (σsq : ℝ) (hσ : 0 < σsq)
    (hv : ‖v‖ ^ 2 ≤ σsq) (d : ℕ) (A : Tensor n d) (hA : IsSymmetricTensor A) (t ρ : ℝ)
    (hρ : 0 < ρ) (hρ' : ρ < 1 / 2) :
    Real.sqrt (∫ z, frobInner (GaussPart.hermiteTensor d z.1) A ^ 2 ∂(gaussCondLaw n v σsq t)) ≤
      ρ ^ (-(d : ℝ) / 2) / Real.sqrt (1 - 2 * ρ) *
        Real.exp (ρ * ‖v‖ ^ 2 * t ^ 2 / (2 * σsq ^ 2 * (1 - 2 * ρ))) *
        GaussPart.frobeniusNorm A := by sorry

end SelfSelReg
