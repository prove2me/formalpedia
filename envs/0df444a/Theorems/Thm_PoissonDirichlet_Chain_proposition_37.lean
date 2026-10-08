-- Prove2me | Theorems.Thm_PoissonDirichlet_Chain_proposition_37
-- name    : PoissonDirichlet.Chain.proposition_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:35.146987+00:00
-- url     : https://prove2.me/theorems/e7f93fef-9376-4c85-bd41-63935275945d
-- title:
--   Proposition 37, p. 886 — independent ratios R_n with (126) make (Y_n) a Markov chain, with co-transition density (128)
-- statement:
--   Let $R_1, R_2, \dots$ be independent random variables that satisfy the a priori constraints (126) almost surely: $0 < R_n < 1$ for all $n$ and $1 + R_1 + R_1R_2 + \cdots < \infty$. Define $Y_n = (1 + R_n + R_nR_{n+1} + \cdots)^{-1}$ as in (125). Then:
--   1. $(Y_n)$ is a Markov chain, typically with inhomogeneous transition probabilities;
--   2. if the $R_n$ are identically distributed, then $(Y_n)$ is stationary, with homogeneous transition probabilities;
--   3. if $R_n$ has density, $P(R_n \in dr) = f_n(r)\,dr$ (127), then $(Y_n)$ has co-transition probabilities
--   $$\frac{P(Y_n \in dy_n \mid Y_{n+1} = y_{n+1})}{dy_n} = 1\Big(0 < y_{n+1} < \frac{y_n}{\bar y_n}\Big)\, f_n\Big(\frac{y_{n+1}\bar y_n}{y_n}\Big)\frac{y_{n+1}}{y_n^2}, \qquad \bar y_n = 1 - y_n. \quad (128)$$
--
--   Applied under $P^*_{\alpha,\theta}$, this gives the Markov property in Theorem 38 (ii).
--
--   **Formalization Note.** The $R_n$ are measurable. Of (126) the hypotheses are $0<R_n<1$ and the summability of $R_1 + R_1R_2 + \cdots$; the third constraint $0 < Y_{n+1} < Y_n/(1-Y_n)$ follows from these two and (125). "Markov chain" is `IsMarkovWith` with Markov kernels; "stationary" means the law of $(Y_{k+1}, Y_{k+2}, \dots)$ equals that of $(Y_1, Y_2, \dots)$ for every $k$ (stated on measurable sets of sequences); "homogeneous" means one kernel for every step. The co-transition (128) is stated in its defining form: for nonnegative measurable $g, h$, $E[h(Y_n)g(Y_{n+1})] = E\big[g(Y_{n+1})\int h(y)\,\rho_n(Y_{n+1}, y)\,dy\big]$ with $\rho_n$ the right side of (128), restricted to $0<y<1$ (outside it the indicator of (128) vanishes in the paper's reading as well). A density $f_n$ is given as a real function whose positive part is the density, through $R_n$ having law $f_n^+\,dr$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 886, Proposition 37, (127), (128); p. 885, (125), (126)

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
import Definitions.Def_PoissonDirichlet_Chain_Markov
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Chain
/-- Proposition 37, p. 886, 0-based. Let `R_1, R_2, …` (here `R 0, R 1, …`) be independent
random variables satisfying the a priori constraints (126) almost surely: `0 < R_n < 1` and
`1 + R_1 + R_1 R_2 + ⋯ < ∞`; let `Y_n = (1 + R_n + R_n R_{n+1} + ⋯)^{-1}` as in (125)
(`YofR (R · ω) k` is `Y_{k+1}`). Then
1. `(Y_n)` is a Markov chain (with possibly inhomogeneous transition kernels);
2. if the `R_n` are identically distributed, `(Y_n)` is stationary, with homogeneous
   transition probabilities;
3. if `R_n` has density `f_n`, (127), then `(Y_n)` has co-transition probabilities (128):
   `P(Y_n ∈ dy_n | Y_{n+1} = y_{n+1}) / dy_n = 1(0 < y_{n+1} < y_n/ȳ_n) f_n(y_{n+1} ȳ_n / y_n)
   y_{n+1} / y_n²`, `ȳ_n = 1 - y_n`. -/
theorem proposition_37 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℕ → Ω → ℝ) (hRm : ∀ n, Measurable (R n)) (hind : iIndepFun R P)
    (h126 : ∀ᵐ ω ∂P, (∀ n, 0 < R n ω ∧ R n ω < 1) ∧
      Summable (fun j : ℕ => ∏ i ∈ Finset.range (j + 1), R i ω)) :
    (∃ κ : ℕ → Kernel ℝ ℝ, (∀ k, IsMarkovKernel (κ k)) ∧
      IsMarkovWith P (fun ω => YofR (fun i => R i ω)) κ) ∧
    ((∀ n, IdentDistrib (R n) (R 0) P P) →
      (∀ k : ℕ, ∀ s : Set (ℕ → ℝ), MeasurableSet s →
        P ((fun ω (j : ℕ) => YofR (fun i => R i ω) (k + j)) ⁻¹' s) =
          P ((fun ω => YofR (fun i => R i ω)) ⁻¹' s)) ∧
      ∃ κ₀ : Kernel ℝ ℝ, IsMarkovKernel κ₀ ∧
        IsMarkovWith P (fun ω => YofR (fun i => R i ω)) (fun _ => κ₀)) ∧
    (∀ k : ℕ, ∀ fk : ℝ → ℝ,
      HasLaw (R k) (volume.withDensity (fun r => ENNReal.ofReal (fk r))) P →
      ∀ g h : ℝ → ENNReal, Measurable g → Measurable h →
        ∫⁻ ω, h (YofR (fun i => R i ω) k) * g (YofR (fun i => R i ω) (k + 1)) ∂P =
          ∫⁻ ω, g (YofR (fun i => R i ω) (k + 1)) *
            (∫⁻ y, ENNReal.ofReal
                (if 0 < y ∧ y < 1 ∧ 0 < YofR (fun i => R i ω) (k + 1) ∧
                    YofR (fun i => R i ω) (k + 1) < y / (1 - y)
                  then fk (YofR (fun i => R i ω) (k + 1) * (1 - y) / y) *
                    YofR (fun i => R i ω) (k + 1) / y ^ 2
                  else 0) * h y ∂volume) ∂P) := by sorry

end PoissonDirichlet.Chain
