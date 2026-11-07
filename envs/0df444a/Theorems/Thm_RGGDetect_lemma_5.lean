-- Prove2me | Theorems.Thm_RGGDetect_lemma_5
-- name    : RGGDetect.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:20.618868+00:00
-- url     : https://prove2.me/theorems/5fc9f832-36cd-4208-8891-5a0da9a989cc
-- title:
--   Lemma 5 — degree truncation
-- statement:
--   There is a constant $C$ depending only on the total degree $2t(D)$ such that, with $I=V^c$ and $T_I$ the truncation (34),
--
--   $$
--   \mathbb E\left[\int_{(T_I)^c}\frac{r^2_{u,I,D}}{\Lambda_{u,I}}\,dQ_I\right]\le C\,n^{-20}\,\mathbb E(D^2)\log^{\nu(D)}(en)=o(g(D)). \tag{35}
--   $$
--
--   Atypically large external degrees of the marked vertex contribute negligibly.
--
--   **Formalization Note** In the regime (1): $C>0$ is chosen after $\delta$ and $t$, before the sequences; $o(g(D))$ is $e_n\,g(D)$ with $e_n\to0$ chosen after the sequences, uniform over every $V$, positive $\boldsymbol\ell$ with $\|\boldsymbol\ell\|_1=2t$, nonzero $D\in\mathcal H_{\boldsymbol\ell}$ and $u\in V$.
--
--   Differences from the source:
--   - generalization: the standing hypotheses (1) of Theorem 1, for all n → sequences in `Regime δ p d τ`: each hypothesis for all large n; reason: the statement is asymptotic, so sequences satisfying (1) for all n are covered
--   - encoding: o(g(D)) → e_n·g(D) with e → 0 chosen after the sequences, uniform over V, ℓ, D, u of half-degree t; reason: the paper's asymptotic notation; the ratio n^{-20} log^ν(en)/(pL^ν) does not depend on D
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 5, eq. (35), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RGGDetect_Regime
import Definitions.Def_RGGDetect_cavity
import Definitions.Def_RGGDetect_harmPoly

open Filter Topology MeasureTheory

namespace RGGDetect

/-- **Lemma 5** (degree truncation; arXiv:2610.08517, held version, sha256 e7bebd4a…, Lemma 5, p.13,
eq. (35)): there is a constant `C` depending only on the total degree `2t(D)` such that
`E[∫_{(T_I)^c} r²_{u,I,D}/Λ_{u,I} dQ_I] ≤ C n^{-20} E(D²) log^{ν(D)}(en) = o(g(D))`, `I = V^c`.

**Formalization Note** In the regime (1): `C` is chosen after `δ` and `t`, before the sequences; the
`o(g(D))` is `e_n g(D)` with `e → 0` chosen after the sequences and uniform over all `V`, `ℓ` with
`‖ℓ‖₁ = 2t`, nonzero `D ∈ H_ℓ` and `u ∈ V`. Both inequalities hold for all large `n`. -/
theorem lemma_5 (δ : ℝ) (hδ : 0 < δ) (t : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : ℕ → ℝ) (d : ℕ → ℕ) (τ : ℕ → ℝ), Regime δ p d τ →
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      ∀ (V : Finset (Fin n)) (ℓ : Fin n → ℕ), (∀ v ∈ V, 1 ≤ ℓ v) → ∑ v ∈ V, ℓ v = 2 * t →
      ∀ D : Config n (d n) → ℝ, D ∈ tensorHarm V ℓ → D ≠ 0 → ∀ u ∈ V,
        cavInt n (d n) (τ n) u Vᶜ D (fun _ y => y ∉ TI n (capProb (d n) (τ n)) Vᶜ) ≤
            C * (n : ℝ) ^ (-20 : ℤ) * (∫ x, D x ^ 2 ∂(prior n (d n))) *
              Real.log (Real.exp 1 * n) ^ nuD V ℓ D ∧
        C * (n : ℝ) ^ (-20 : ℤ) * (∫ x, D x ^ 2 ∂(prior n (d n))) *
              Real.log (Real.exp 1 * n) ^ nuD V ℓ D ≤ e n * gD (τ n) V ℓ D := by sorry

end RGGDetect
