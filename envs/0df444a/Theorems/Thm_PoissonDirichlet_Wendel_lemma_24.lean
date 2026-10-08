-- Prove2me | Theorems.Thm_PoissonDirichlet_Wendel_lemma_24
-- name    : PoissonDirichlet.Wendel.lemma_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:58.164978+00:00
-- url     : https://prove2.me/theorems/2487d7e9-9486-42c0-a46e-32a07e5badcb
-- title:
--   Lemma 24 (i)–(ii), p. 870 — CΔ_n^{−α} is gamma(n); Δ_i/Δ_n are order statistics of α x^{−α−1}1(x>1), independent of (Δ_n, Δ_{n+1}, …)
-- statement:
--   Let $\alpha>0$, $C>0$, and let $\Delta_1>\Delta_2>\cdots$ be the ranked points of a Poisson random measure $\Lambda_\alpha$ on $(0,\infty)$ with $\Lambda_\alpha(x,\infty)=Cx^{-\alpha}$. Then:
--
--   1. (i) for every $n\ge1$, $C\Delta_n^{-\alpha}$ has the gamma$(n)$ distribution (shape $n$, rate $1$);
--   2. (ii) for every $n\ge2$, the vector of ratios
--   $$\left(\frac{\Delta_1}{\Delta_n}>\frac{\Delta_2}{\Delta_n}>\cdots>\frac{\Delta_{n-1}}{\Delta_n}\right)$$
--   has the law of the decreasing order statistics of $n-1$ independent variables with common law $C^{-1}\Lambda_\alpha(dx)1(x>1)=\alpha x^{-\alpha-1}dx\,1(x>1)$, and this vector is independent of the sequence $(\Delta_n,\Delta_{n+1},\dots)$.
--
--   Part (ii) is what makes $A_{n-1}$ of Proposition 11 a sum of $n-1$ i.i.d. terms; part (i) supplies the mixing law in the proof of (37).
--
--   **Formalization Note** The ranked points $\Delta_1>\Delta_2>\cdots$ of a Poisson random measure $\Lambda_\alpha$ on $(0,\infty)$ with $\Lambda_\alpha(x,\infty)=Cx^{-\alpha}$ are represented through the arrival times of a unit-rate Poisson process, as in (27)–(28) of the paper: $X_n=\varepsilon_1+\cdots+\varepsilon_n$ with $\varepsilon_i$ i.i.d. standard exponential, and $\Delta_n=(C/X_n)^{1/\alpha}$, so that $X_n=C\Delta_n^{-\alpha}=\Lambda_\alpha(\Delta_n,\infty)$. No general Poisson random measure is built. Under this representation part (i) says that $X_n$ is gamma$(n)$. The decreasing order statistics of $x_1,\dots,x_{n-1}$ are computed by the ranking map of the definitions file applied to $(x_1,\dots,x_{n-1},0,0,\dots)$; the equality of laws is stated set-by-set through preimages. Part (iii) of Lemma 24 (a conditional Poisson statement) is not stated; its consequence (67) is a separate item. 0-based: `prmPoint α C ε k` is $\Delta_{k+1}$, and part (ii) is stated for $n=k+2$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 870, Lemma 24 (i), (ii)

import Mathlib
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Wendel

/-- Lemma 24 (i), (ii), p. 870, for the PoissonDirichlet.Ratio.ranked points `Δ_n` of a PRM `Λ_α` on (0, ∞) with
`Λ_α(x, ∞) = C x^{-α}`, represented as `Δ_{k+1} = (C / X_{k+1})^{1/α}` with `X_{k+1}` the
arrival times of a unit Poisson process ((27)–(28)). (i) `C Δ_n^{-α}` is gamma(n);
(ii) for n = k + 2 ≥ 2 the ratios `Δ_i / Δ_n`, i < n, are distributed as the decreasing order
statistics of n − 1 i.i.d. variables with density `α x^{-α-1}` on (1, ∞), independently of
`(Δ_n, Δ_{n+1}, …)`. 0-based: `prmPoint α C ε k` is `Δ_{k+1}`. -/
theorem lemma_24 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α C : ℝ) (hα : 0 < α) (hC : 0 < C) (ε : ℕ → Ω → ℝ) (hind : iIndepFun ε P)
    (hlaw : ∀ i, HasLaw (ε i) (expMeasure 1) P) :
    (∀ k : ℕ, HasLaw (fun ω => C * prmPoint α C ε k ω ^ (-α))
        (gammaMeasure ((k : ℝ) + 1) 1) P) ∧
    (∀ k : ℕ,
      (∀ s : Set (Fin (k + 1) → ℝ), MeasurableSet s →
        P ((fun ω (i : Fin (k + 1)) => prmPoint α C ε i ω / prmPoint α C ε (k + 1) ω) ⁻¹' s) =
          (Measure.pi fun _ : Fin (k + 1) => tailLaw α)
            ((fun (x : Fin (k + 1) → ℝ) (i : Fin (k + 1)) =>
              PoissonDirichlet.Ratio.ranked (fun j : ℕ => if h : j < k + 1 then x ⟨j, h⟩ else 0) i) ⁻¹' s)) ∧
      IndepFun (fun ω (i : Fin (k + 1)) => prmPoint α C ε i ω / prmPoint α C ε (k + 1) ω)
        (fun ω (m : ℕ) => prmPoint α C ε (k + 1 + m) ω) P) := by sorry

end PoissonDirichlet.Wendel
