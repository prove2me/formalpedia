-- Prove2me | Theorems.Thm_TeschlQM_Free_free_asymptotics
-- name    : TeschlQM.Free.free_asymptotics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T01:15:52.058539+00:00
-- url     : https://prove2.me/theorems/9ccb79c5-d574-4cd2-ac19-0a623633e1f3
-- title:
--   Lemma 7.10 — long-time asymptotics of e^{−itH₀}ψ in L²
-- statement:
--   For every $\psi \in L^2(\mathbb R^n)$,
--   $$e^{-itH_0}\psi(x) - \Big(\frac{1}{2it}\Big)^{n/2} e^{i\frac{x^2}{4t}}\, \hat\psi\Big(\frac{x}{2t}\Big) \to 0$$
--   in $L^2(\mathbb R^n)$ as $|t| \to \infty$. Here $e^{-itH_0} = \mathcal F^{-1} e^{-itp^2}\mathcal F$ and $\hat\psi$ is the $L^2$ Fourier transform, both in the normalization $\hat f(p) = (2\pi)^{-n/2}\int e^{-ipx}f(x)\,d^nx$.
--
--   Physically: the probability of finding the particle in a region $\Omega$ is asymptotically the probability of finding its momentum in $\frac{1}{2t}\Omega$.
--
--   **Formalization Note.** $e^{-itH_0}$ is `timeEvolution n t` and $\hat\psi$ is `fourierL2 n ψ`. $(1/(2it))^{n/2}$ is $(\sqrt{1/(2it)})^n$ with the principal square root, the convention of Lemma 7.3 from which (7.30) and (7.32) are derived. Convergence in $L^2$ is `eLpNorm … 2 volume → 0`, and $|t| \to \infty$ is the filter `cocompact ℝ`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 169, Lemma 7.10

import Mathlib
import Definitions.Def_TeschlQM_Free_fourier
import Definitions.Def_TeschlQM_Free_timeEvolution

namespace TeschlQM.Free

open MeasureTheory Filter Topology

/-- Teschl, Lemma 7.10, p. 169: for every `ψ ∈ L²(ℝⁿ)`,
`e^{-itH₀}ψ(x) - (1/(2it))^{n/2} e^{ix²/(4t)} ψ̂(x/(2t)) → 0` in `L²` as `|t| → ∞` (7.33).
`e^{-itH₀}` is `F⁻¹ e^{-itp²} F` (7.27) (`timeEvolution`), `ψ̂` is the `L²` Fourier transform in
Teschl's normalization (`fourierL2`), `(1/(2it))^{n/2}` is `(√(1/(2it)))ⁿ` with the principal
square root (the convention of Lemma 7.3), and `|t| → ∞` is the filter `cocompact ℝ`. -/
theorem free_asymptotics (n : ℕ) (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Tendsto
      (fun t : ℝ => eLpNorm
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (timeEvolution n t ψ : EuclideanSpace ℝ (Fin n) → ℂ) x -
            ((1 / (2 * Complex.I * t)) ^ (1 / 2 : ℂ)) ^ n *
              Complex.exp (Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) / (4 * t)) *
              fourierL2 n ψ ((2 * t)⁻¹ • x))
        2 volume)
      (cocompact ℝ) (𝓝 0) := by sorry

end TeschlQM.Free
