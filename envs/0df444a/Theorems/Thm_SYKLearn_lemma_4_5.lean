-- Prove2me | Theorems.Thm_SYKLearn_lemma_4_5
-- name    : SYKLearn.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:06.902819+00:00
-- url     : https://prove2.me/theorems/2872c204-54cc-495b-b539-544a19f7e2aa
-- title:
--   Lemma 4.5 — derivative lower bound: $\frac{d}{da}\mathrm{AvgScore}_{\tilde\rho}(a)\ge\frac\mu2e^{-2\beta C/\mu}$ on $[1/2,2]$
-- statement:
--   Let $\tilde H$ be Hermitian, $\beta>0$, $\alpha\in[3/4,5/4]$, and let $\mathcal D$ be the law of the energy difference in Experiment 1 with measured Hamiltonian $\tilde H$ and input state $\tilde\rho=\rho_{\beta\alpha}(\tilde H)$. Suppose there are $\mu,C>0$ with
--
--   $$\mathbb E_{\delta\sim\mathcal D}\,\delta\ge\mu,\qquad \mathbb E_{\delta\sim\mathcal D}\,\delta^2\le C.$$
--
--   Then for every $a\in[1/2,2]$,
--
--   $$\frac{d}{da}\mathrm{AvgScore}_{\tilde\rho}(a)\ \ge\ \frac\mu2\,e^{-2\beta C/\mu}.$$
--
--   The average score is therefore not flat near its zero, so an additive error in the score translates into a proportional error in the recovered scale.
--
--   **Formalization Note** The condition $\alpha\in[3/4,5/4]$ is §4's standing assumption (p.34). The derivative is Mathlib's `deriv` of $a\mapsto\mathrm{AvgScore}(a)$.
--
--   Differences from the source:
--   - generalization: the candidate Hamiltonian H̃ = σ_n√m Σ d̂_I Γ_I of §4 and the SYK Majoranas → any Hermitian matrix K on ℂ^{2^{n/2}} and the Majoranas of any Model; reason: the proof uses only detailed balance of the Gibbs state of K, which holds for every Hermitian K; specializing K gives the page's statement
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 4.5, p.36 (proof p.37)

import Mathlib
import Definitions.Def_SYKLearn_Experiment

noncomputable section
open MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma 4.5 (Derivative lower bound, AvgScore)**, p.36 (Anshu–Arunachalam–Chen–Hwang,
*Efficiently Learning SYK Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). Let
`D` be the distribution when sampling `δ` from Experiment 1, when samples correspond to the Gibbs
state `ρ̃ = ρ_{βα}(H̃)`. Suppose there exist `µ, C > 0` such that `E_{δ∼D} δ ≥ µ` and
`E_{δ∼D} δ² ≤ C`. Under this assumption, for every `a ∈ [1/2, 2]`,
`(d/da) AvgScore_ρ̃(a) ≥ (µ/2)e^{−2βC/µ}`.

**Formalization Note.** `D = energyLaw Q.γ K (gibbs K (β α))` with candidate Hamiltonian
`H̃ = K` (any Hermitian matrix), the model's Majoranas, and the physical Gibbs state at inverse
temperature `βα`. `α ∈ [3/4, 5/4]` is §4's standing assumption (p.34, "we use this assumption
throughout this section"). The derivative is `deriv` of `a ↦ AvgScore(a)`. `β > 0`. -/
theorem lemma_4_5 {N : ℕ} (Q : Model N) (K : Mat (SiteHilbert N)) (hK : K.IsHermitian)
    (β α μ C : ℝ) (hβ : 0 < β) (hα : 3 / 4 ≤ α ∧ α ≤ 5 / 4) (hμ : 0 < μ) (hC : 0 < C)
    (h1 : μ ≤ ∫ δ, δ ∂(energyLaw Q.γ K (gibbs K (β * α))))
    (h2 : ∫ δ, δ ^ 2 ∂(energyLaw Q.γ K (gibbs K (β * α))) ≤ C) :
    ∀ a ∈ Set.Icc (1 / 2 : ℝ) 2,
      μ / 2 * Real.exp (-(2 * β * C / μ)) ≤
        deriv (fun a => avgScore β a (energyLaw Q.γ K (gibbs K (β * α)))) a := by sorry

end SYKLearn
