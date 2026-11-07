-- Prove2me | Theorems.Thm_QPSpinParisi_lemma_3_6
-- name    : QPSpinParisi.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:22:59.729446+00:00
-- url     : https://prove2.me/theorems/c4d3a06f-3803-4612-8e85-65e0964773dd
-- title:
--   Lemma 3.6 — $\liminf_{\beta\to\infty}\Psi_{\xi,\beta,\alpha_{\xi,\beta}}(0,0)\ge\Psi_{\xi,\gamma}(0,0)+\upsilon/2$
-- statement:
--   With $\gamma$ and $\upsilon$ defined by (3.30),
--   $$\liminf_{\beta\to\infty}\Psi_{\xi,\beta,\alpha_{\xi,\beta}}(0,0)\ge\Psi_{\xi,\gamma}(0,0)+\frac\upsilon2.$$
--   The atom $\upsilon\delta_1$ in the limit contributes $\upsilon/2$, which cancels the contribution of the same atom in the second term of the functional. This is the lower bound of the zero-temperature limit.
--
--   Differences from the source:
--   - generalization: one Brownian motion $B$ on an unnamed space → every `BrownianNoise`, on every probability space; reason: the source's $B$ is one such object, and `exists_noise` makes the statement non-vacuous
--   - generalization: $Y_n$ built as $\sum_pc_pY_{n,p}$ → every centered Gaussian field with covariance $n\xi(q(s,t))$ and continuous paths; reason: only the covariance is used; the source's field is one such field, and `exists_overlapField` makes the statement non-vacuous
--   - encoding: $\limsup$ / $\liminf$ → an eventual bound for each $\varepsilon>0$; reason: the same statement, without default values of a real $\limsup$
--   - reading: "$\beta\to\infty$" → the sequence along which (3.30) holds; reason: (3.30) holds along a subsequence, which is what "defined by (3.30)" refers to
--   - generalization: $\gamma,\upsilon$ produced by the subsequence extraction → any $\gamma\in\mathcal U$ and real $\upsilon$ for which the convergence (3.30) holds along the sequence (which forces $\upsilon\ge0$); reason: the source's $\gamma,\upsilon$ are such a pair
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.6, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_IsMinB
import Definitions.Def_QPSpinParisi_USet
import Definitions.Def_QPSpinParisi_Psi
import Definitions.Def_QPSpinParisi_gamBeta

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.6, p.22, PDF p.22: with `γ` and `υ` defined by (3.30), `liminf_{β→∞} Ψ_{ξ,β,α_{ξ,β}}(0, 0) ≥ Ψ_{ξ,γ}(0, 0) + υ/2`.

**Formalization Note** The hypothesis `hconv` is (3.30) itself along the sequence `βs`, and it already forces `υ ≥ 0`. The liminf is taken along that sequence: the printed
"`β → ∞`" refers to the subsequence of (3.30). The liminf bound is written as an eventual bound for each `ε > 0`. -/
theorem lemma_3_6 (c : ℕ → ℝ) (hc : MixHyp c) (W : BrownianNoise c) (al : ℝ → Icc (0 : ℝ) 1 → ℝ)
    (hal : ∀ β : ℝ, 0 < β → IsMinB W β (al β)) (βs : ℕ → ℝ) (hβs : Tendsto βs atTop atTop)
    (γ : Ico (0 : ℝ) 1 → ℝ) (hγ : γ ∈ USet) (υ : ℝ)
    (hconv : ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 1) →
      Tendsto (fun k => ∫ q in (0 : ℝ)..1, f q * zeta c q * gamHat (gamBeta (βs k) (al (βs k))) q)
        atTop (𝓝 ((∫ q in (0 : ℝ)..1, f q * zeta c q * gamHat γ q) + υ * f 1)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, Psi W γ 0 0 + υ / 2 - ε ≤ PsiB W (βs k) (al (βs k)) 0 0 := by sorry

end QPSpinParisi
