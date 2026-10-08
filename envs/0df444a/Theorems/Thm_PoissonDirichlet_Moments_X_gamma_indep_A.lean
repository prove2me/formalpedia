-- Prove2me | Theorems.Thm_PoissonDirichlet_Moments_X_gamma_indep_A
-- name    : PoissonDirichlet.Moments.X_gamma_indep_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:01.915026+00:00
-- url     : https://prove2.me/theorems/92d03bbf-2e00-46c4-8da4-e3c334099c25
-- title:
--   Proof of Lemma 27, p. 875 — X_n = LV_n^{−α} is gamma(n) and independent of A_{n−1}
-- statement:
--   Let $0<\alpha<1$ and let $(V_n)$ have the $\mathrm{PD}(\alpha,0)$ law, with local time $L=\lim_n nV_n^\alpha$ (24), $X_n=LV_n^{-\alpha}$ (27) and $A_{n-1}=(V_1+\dots+V_{n-1})/V_n$ (31). For every $n\ge1$:
--
--   1. $X_n$ has the $\mathrm{gamma}(n)$ distribution, with density $x^{n-1}e^{-x}/\Gamma(n)$ on $(0,\infty)$;
--   2. $X_n$ is independent of $A_{n-1}$.
--
--   The paper uses this fact in the proof of Lemma 27 ("the fact that $X_n$ has gamma($n$) distribution independent of $A_{n-1}$"); it follows from Proposition 10 (iii), where $X_n$ is the $n$-th arrival time of a unit Poisson process, and from Corollary 23.
--
--   **Formalization Note** The gamma law is Mathlib's gamma measure with shape $n$ and rate $1$. Indexing is from $0$: the Lean index $k$ is $n-1$. $L$ enters only through its defining limit (24).
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 875, proof of Lemma 27, first sentence

import Mathlib
import Definitions.Def_PoissonDirichlet_Moments_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

/-- Proof of Lemma 27, p. 875, 0-based (`k = n - 1`): under `PD(α, 0)`, with `L` the local
time (24), `X_n = L V_n^{-α}` has the gamma(n) law (shape `n`, rate 1) and is independent of
`A_{n-1}`. -/
theorem X_gamma_indep_A {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V ω k ^ α) atTop (𝓝 (L ω)))
    (k : ℕ) :
    HasLaw (fun ω => Xseq α (L ω) (V ω) k) (gammaMeasure ((k : ℝ) + 1) 1) P ∧
      IndepFun (fun ω => Xseq α (L ω) (V ω) k) (fun ω => PoissonDirichlet.Wendel.Aseq (V ω) k) P := by sorry

end PoissonDirichlet.Moments
