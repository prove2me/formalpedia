-- Prove2me | Theorems.Thm_StochKolmogorov_Classify_lemma_5_1
-- name    : StochKolmogorov.Classify.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:59.189428+00:00
-- url     : https://prove2.me/theorems/a3f31243-9bd9-4b67-96f9-8144190b3a71
-- title:
--   Lemma 5.1, p. 20 — for every µ ∈ M and i ∈ I_µ, λᵢ(µ) = 0
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i = X_i f_i(X)\,dt + X_i g_i(X)\,dE_i$, $i = 1,\dots,n$ ($n \ge 1$), on $\mathbb R^n_+ = [0,\infty)^n$, with $E = \Gamma^\top B$ for a standard Brownian motion $B$ and $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$; $X^x$ denotes the solution started at $x$, and the coefficients satisfy Assumption 1.1 with the vector $c \in \mathbb R^{n,\circ}_+$ and the constant $\gamma_b > 0$ of (1.2). For every boundary ergodic measure $\mu \in \mathcal M$ and every species $i \in I_\mu$ charged by $\mu$,
--   $$
--   \lambda_i(\mu) = \int\Big(f_i(x) - \frac{\sigma_{ii}g_i^2(x)}{2}\Big)\mu(dx) = 0 .
--   $$
--
--   Inside the support of an ergodic measure the species present neither grow nor decay on average. In the proof of Lemma 5.8 this kills the contribution of $\mu$ itself in (5.26).
--
--   **Formalization Note** The standing setting is carried by explicit hypotheses: `hn : 0 < n`, a family `X x` of strong solutions from every $x \in \mathbb R^n_+$ driven by one Brownian motion `B` (`IsSolutionFamily`), and `Assumption11 C c γb`. Coordinates are indexed by `Fin n` (0-based), and $\|x\| = \sum_i |x_i|$ is the $\ell^1$ norm `l1` of p. 4. The integrability of $f_i - \sigma_{ii}g_i^2/2$ under $\mu$ (which the paper obtains from Lemma 3.3, "λᵢ(µ) is well-defined") is stated as part of the conclusion, so that the identity is not satisfied by the default value of a non-integrable Bochner integral.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 5.1, p. 20 (= Lemma 2.1, p. 8)

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

theorem lemma_5_1 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    ∀ μ ∈ bdryErgodic P X, ∀ i ∈ supp μ,
      Integrable (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) μ ∧ lyap C i μ = 0 := by sorry

end StochKolmogorov.Classify
