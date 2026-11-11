-- Prove2me | Theorems.Thm_QuadSDE_lemma_4
-- name    : QuadSDE.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:06.07196+00:00
-- url     : https://prove2.me/theorems/4b0807d9-eb55-4432-b49f-015f4b5eb59b
-- title:
--   Lemma 4 — density $\mu(1+h_t)$ of the rescaled process, $\|h_t\|_{L^2(\mu)}\le R_0$, and $\frac d{dt}\langle\varphi,h_t\rangle_\mu=\langle G_t\varphi,h_t\rangle_\mu$
-- statement:
--   Let the drift be admissible, $0<p,q\le1$, $Y\in\mathbb R^N$, let $(W,Z)$ be the noise of APX-SDE and let $X$ solve $dX=f(X)\,dt+\sqrt q\,dW$, $X(0)=Y+\sqrt pZ$, on every horizon. Put $\rho(t)=p+qt$, $\lambda(t)=q/(2\rho(t))$, $\tilde X(t)=X(t)/\sqrt{\rho(t)}$, $y=Y/\sqrt p$, and let $\mu$ be the standard Gaussian density. There are functions $h_t$, $t\ge0$, such that:
--   1. for every $t\ge0$, $\tilde X(t)$ has the probability density
--   $$\tilde\pi_t(x)=\mu(x)\big(1+h_t(x)\big),\qquad\int_{\mathbb R^N}h_t(x)\mu(x)\,dx=0,\qquad\|h_t\|_{L^2(\mu)}\le R_0:=\sqrt{e^{\|y\|^2}-1}\qquad(30),$$
--   with $1+h_t\ge0$ almost everywhere and $h_t\in L^2(\mu)$;
--   2. initially $h_0(x)=\mu(x-y)/\mu(x)-1$ for almost every $x$;
--   3. for every real polynomial $\varphi$ and every $t\ge0$,
--   $$\frac d{dt}\langle\varphi,h_t\rangle_\mu=\langle G_t\varphi,h_t\rangle_\mu,\qquad G_t=\lambda(t)(\Delta-x\cdot\nabla)+\sqrt{\rho(t)}\,f\cdot\nabla\qquad(31).$$
--
--   The correction $h_t$ carries all the information about the law of the SDE; the rest of the analysis computes its Hermite coefficients.
--
--   Differences from the source:
--   - generalization: X(t) solves the SDE Eq. (2) ("a unique global strong solution", p. 17) → any process X on any probability space carrying (W, Z) that solves Eq. (2) pathwise (continuous paths, integral equation a.s.); reason: with additive noise and a locally Lipschitz drift every pathwise solution agrees a.s. with the strong solution, so the statement specializes to the source's
--   - reading: X̃(t) has a PDF of the form μ(1 + h_t), ‖h_t‖_{L²(μ)} ≤ R₀, initially h₀ = μ(x − y)/μ(x) − 1 → the law of X̃(t) equals Lebesgue measure with density μ(1 + h_t), 1 + h_t ≥ 0 a.e., h_t ∈ L²(μ) with ∫ h_t² dμ ≤ R₀², and h₀ equal to μ(· − y)/μ − 1 Lebesgue-a.e.; reason: a PDF is a nonnegative Lebesgue density, determined only almost everywhere
--   - reading: d/dt ⟨φ, h_t⟩_μ for t ≥ 0 → derivative of s ↦ ⟨φ, h_s⟩_μ within [0, ∞) at every t ≥ 0 (from the right at 0), for every real polynomial φ; reason: t ranges over [0, ∞)
--   - encoding: indices in [N], time t ≥ 0 → Fin N (0-based), process time ℝ≥0, ODE time ℝ on [0, T]; reason: Lean convention; same instances
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.1, Lemma 4, p. 18

import Mathlib
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_NoisySDE
import Definitions.Def_QuadSDE_Frame
import Definitions.Def_QuadSDE_GaussHermite
import Definitions.Def_QuadSDE_Generator

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuadSDE

/-- **Lemma 4 (density of the rescaled process).**
Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.1, Lemma 4, p. 18: "For
every `t ≥ 0`, the rescaled process `X̃(t)` has a PDF of the form `π̃_t(x) = µ(x)(1 + h_t(x))`,
`∫_{ℝ^N} h_t(x)µ(x) dx = 0`, `‖h_t‖_{L²(µ)} ≤ R₀ := √(e^{‖y‖²} − 1)`. (30) Initially
`h₀(x) = µ(x − y)/µ(x) − 1`. For every polynomial `φ`, `d/dt ⟨φ, h_t⟩_µ = ⟨G_t φ, h_t⟩_µ`,
`G_t = λ(t)(∆ − x · ∇) + √ρ(t) f · ∇`. (31)"

Setting of APX-SDE: an admissible drift, `0 < p, q ≤ 1`, `Y ∈ ℝ^N`, noise `(W, Z)` as in Eq. (2),
and `X` solving Eq. (2) with `X(0) = Y + √p Z` on every horizon. Let `ρ(t) = p + qt`,
`λ(t) = q/(2ρ(t))`, `X̃(t) = X(t)/√ρ(t)`, `y = Y/√p`, and `µ` the standard Gaussian density. Then
there are functions `h_t` (`t ≥ 0`) such that
1. for every `t ≥ 0`: `X̃(t)` has density `µ(1 + h_t)` with `1 + h_t ≥ 0` a.e.; `h_t ∈ L²(µ)`;
   `∫ h_t µ = 0`; and `‖h_t‖²_{L²(µ)} ≤ R₀²`;
2. `h₀(x) = µ(x − y)/µ(x) − 1` for almost every `x`;
3. for every real polynomial `φ` and every `t ≥ 0`, `s ↦ ⟨φ, h_s⟩_µ` has derivative
   `⟨G_t φ, h_t⟩_µ` at `t` (from the right at `t = 0`).

**Formalization Note.** "Has PDF `π`" is `P.map X̃(t) = volume.withDensity π`. `⟨g, h⟩_µ` is the
integral against the standard Gaussian measure `gaussPi N`; `G_t φ` is the polynomial `genPoly`.
Times of the process are `ℝ≥0`; the derivative is taken in the real variable `s ≥ 0`, with
`h_s = h_{s.toNNReal}`. -/
theorem lemma_4 {N : ℕ} (c : Coeff N) (hc : IsAdmissibleDrift c) (p q : ℝ) (hp : 0 < p)
    (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) (Y : Fin N → ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → Fin N → ℝ) (Z : Ω → Fin N → ℝ)
    (hBZ : NoiseSetting P B Z) (X : ℝ≥0 → Ω → Fin N → ℝ)
    (hX : ∀ T : ℝ≥0, SolvesPathwise P (drift c) q B (fun ω => Y + Real.sqrt p • Z ω) X T) :
    ∃ h : ℝ≥0 → (Fin N → ℝ) → ℝ,
      (∀ t : ℝ≥0,
        P.map (fun ω => (Real.sqrt (rho p q t))⁻¹ • X t ω) =
            volume.withDensity (fun x => ENNReal.ofReal (gaussDensity x * (1 + h t x))) ∧
          (∀ᵐ x ∂(volume : Measure (Fin N → ℝ)), 0 ≤ 1 + h t x) ∧
          MemLp (h t) 2 (gaussPi N) ∧
          ∫ x, h t x ∂gaussPi N = 0 ∧
          ∫ x, h t x ^ 2 ∂gaussPi N ≤ R0 p Y ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (Fin N → ℝ)),
        h 0 x = gaussDensity (x - yvec p Y) / gaussDensity x - 1) ∧
      ∀ (φ : MvPolynomial (Fin N) ℝ) (t : ℝ), 0 ≤ t →
        HasDerivWithinAt (fun s : ℝ => ∫ x, MvPolynomial.eval x φ * h s.toNNReal x ∂gaussPi N)
          (∫ x, MvPolynomial.eval x (genPoly c p q t φ) * h t.toNNReal x ∂gaussPi N)
          (Set.Ici 0) t := by sorry

end QuadSDE
