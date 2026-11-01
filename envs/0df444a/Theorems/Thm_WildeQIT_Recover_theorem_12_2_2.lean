-- Prove2me | Theorems.Thm_WildeQIT_Recover_theorem_12_2_2
-- name    : WildeQIT.Recover.theorem_12_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:48.791168+00:00
-- url     : https://prove2.me/theorems/ff6ef785-0dcf-42b3-be9a-ed21df27ada7
-- title:
--   Theorem 12.2.2 (Hirschman) (corrected: continuity on the closed strip)
-- statement:
--   Let $S=\{z\in\mathbb C:0<\operatorname{Re}z<1\}$ be the standard strip and $\overline S$ its closure. Let $f:\overline S\to\mathbb C$ be bounded on $\overline S$, holomorphic on $S$, and continuous on $\overline S$. For $\theta\in(0,1)$ put
--
--   $$
--   \alpha_\theta(t)=\frac{\sin(\pi\theta)}{2(1-\theta)\,[\cosh(\pi t)-\cos(\pi\theta)]},
--   \qquad
--   \beta_\theta(t)=\frac{\sin(\pi\theta)}{2\theta\,[\cosh(\pi t)+\cos(\pi\theta)]}.
--   $$
--
--   Then
--
--   $$
--   \ln|f(\theta)|\le\int_{-\infty}^{\infty}dt\left(\alpha_\theta(t)\ln\!\left[|f(it)|^{1-\theta}\right]+\beta_\theta(t)\ln\!\left[|f(1+it)|^{\theta}\right]\right).
--   $$
--
--   The densities $\alpha_\theta,\beta_\theta$ are probability densities, so this is a strengthening of the Hadamard three-lines theorem: the logarithm at an interior point is bounded by an average, not a supremum, of the boundary logarithms. It is the scalar case of the Stein–Hirschman interpolation theorem used in the proof of the recoverability theorem.
--
--   **Formalization Note** $f$ is a function on $\mathbb C$, of which only the values on $\overline S$ enter. $\ln0=-\infty$, and the integral is the extended integral of the positive part minus that of the negative part; the positive part is finite because $f$ is bounded, and the integral may equal $-\infty$. The densities, the extended logarithm and the integral are the published definitions of the Junge–Renner–Sutter–Wilde–Winter formalization.
--
--   Differences from the source:
--   - correction: "continuous on the boundary $\partial\overline S$" → continuous on the closed strip $\overline S$; reason: read literally the statement is false: $f=1$ on $S$ and $f=0$ on $\partial\overline S$ is bounded, holomorphic on $S$ and continuous on $\partial\overline S$, but at $\theta=1/2$ it gives $0\le-\infty$.
--   - encoding: $f:\overline S\to\mathbb C$ → $f:\mathbb C\to\mathbb C$, hypotheses only on $\overline S$; reason: values off $\overline S$ enter neither hypotheses nor conclusion.
--   - encoding: Lebesgue integral of a possibly $-\infty$ integrand → positive-part minus negative-part extended integral, $\ln 0=-\infty$; reason: the book's integral has value in $[-\infty,\infty)$; this represents it without Lean's default value for non-integrable functions.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 12.2.2, (12.14)–(12.16), p. 369

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
open QAlgorithms.Papers.Independent.Dependency50.P21 (alphaDensity betaDensity extendedLog upperLogIntegral)

namespace WildeQIT.Recover

/-- **Theorem 12.2.2 (Hirschman)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Theorem 12.2.2, (12.14)–(12.16), p. 369). Let `S = {z : 0 < Re z < 1}` and
`f : S̄ → ℂ` be bounded on `S̄`, holomorphic on `S` and continuous on `S̄`. Then for `θ ∈ (0, 1)`,
`ln |f(θ)| ≤ ∫ dt (α_θ(t) ln[|f(it)|^{1−θ}] + β_θ(t) ln[|f(1 + it)|^θ])`, with
`α_θ(t) = sin(πθ) / (2(1 − θ)[cosh(πt) − cos(πθ)])` and
`β_θ(t) = sin(πθ) / (2θ[cosh(πt) + cos(πθ)])`.

**Formalization Note** `f` is a function on `ℂ`; only its values on `S̄` enter. "Continuous on the
boundary" is read as continuity on the closed strip (`DiffContOnCl`), the standard hypothesis; the
literal reading is false (see the item's differences). `ln 0 = −∞` (`extendedLog`), and the
integral is the signed extended integral `∫⁺ − ∫⁻` (`upperLogIntegral`), whose positive part is
finite because `f` is bounded; it may equal `−∞`. These and the densities are the published
definitions of Junge–Renner–Sutter–Wilde–Winter (2018). -/
theorem theorem_12_2_2 (f : ℂ → ℂ)
    (hbdd : Bornology.IsBounded (f '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hf : DiffContOnCl ℂ f {z : ℂ | 0 < z.re ∧ z.re < 1})
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    extendedLog ‖f θ‖ ≤
      upperLogIntegral (fun t =>
        (alphaDensity θ t : EReal) * extendedLog (‖f ((t : ℂ) * Complex.I)‖ ^ (1 - θ)) +
        (betaDensity θ t : EReal) * extendedLog (‖f (1 + (t : ℂ) * Complex.I)‖ ^ θ)) := by sorry

end WildeQIT.Recover
