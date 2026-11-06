-- Prove2me | Theorems.Thm_SKWeakPoincare_lemma_6_6
-- name    : SKWeakPoincare.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:40:10.279207+00:00
-- url     : https://prove2.me/theorems/b81b0faf-bec5-4760-aa40-98539df2ddd9
-- title:
--   Lemma 6.6 — warm start from a weak Poincaré inequality (corrected: $\delta\ge0$)
-- statement:
--   Let $P$ be a reversible Markov kernel on a finite space, with stationary law $\mu$ and spectrum in $[0,1]$. Suppose that for every $f$,
--   $$
--   \mathrm{Var}_\mu[f]\le A_0\,\mathcal E_\mu(f,f)+\delta\operatorname{osc}(f)^2,\qquad\mathcal E_\mu(f,f)=\langle f,(I-P)f\rangle_\mu,
--   $$
--   with $A_0\ge1$ and $\delta\ge0$. Then for every $B_0$-warm initial law $\mu_{\mathrm{init}}$ and every integer $k\ge0$,
--   $$
--   d_{\mathrm{TV}}\big(\mu_{\mathrm{init}}P^k,\mu\big)\le\frac12\Big(e^{-k/A_0}(B_0-1)+\delta B_0^2\Big)^{1/2}.
--   $$
--
--   This is a discrete-time, finite-state version of [HMRW25, Theorem 4.6], and one stage of the simulated-annealing bound (Lemma 6.7).
--
--   **Formalization Note** Spectrum in $[0,1]$ is the quadratic-form condition $\langle f,Pf\rangle_\mu\ge0$; the upper bound $\langle f,Pf\rangle_\mu\le\langle f,f\rangle_\mu$ is automatic for a reversible Markov kernel.
--
--   Differences from the source:
--   - correction: no sign condition on δ → 0 ≤ δ; reason: the printed statement is false for δ < 0: on {true, false} with μ uniform, P(x,y) = 1/2, A₀ = 2, δ = −1/4, μinit the point mass at true (2-warm) and k = 0, every hypothesis holds (Var_μ[f] = (f(true) − f(false))²/4 = 2𝓔 − ¼osc²) but d_TV(μinit, μ) = 1/2 > 0 = ½(e⁰(2 − 1) − ¼·4)^{1/2}; proved in Solutions/verification/SKWeakPoincare_sanity.lean; the paper's WPIs all have δ ≥ 0 (Lemma 6.1: a_n, δ_n ≥ 0)
--   - encoding: a reversible Markov kernel P with stationary law μ → IsLaw μ, IsStochastic P and IsReversible μ P; reason: detailed balance for a stochastic matrix makes μ stationary
--   - encoding: spectrum in [0,1] → HasNonnegSpectrum μ P (⟨f, Pf⟩_μ ≥ 0 for all f); reason: a reversible P is self-adjoint in L²(μ) with ⟨f, Pf⟩_μ ≤ ⟨f, f⟩_μ, so the spectrum lies in [0,1] iff the form is nonnegative
--   - encoding: μinit B₀-warm: μinit(S) ≤ B₀μ(S) for all measurable S → IsLaw μinit and μinit(x) ≤ B₀μ(x) for all x; reason: equivalent on a finite space
--   - encoding: a finite space → a Fintype α with [Nonempty α]; reason: a finite space carrying a probability law is nonempty, and osc needs a nonempty space
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Lemma 6.6, p.42 (proof pp.42–43; [HMRW25, Theorem 4.6])

import Mathlib
import Definitions.Def_SKWeakPoincare_fMean

namespace SKWeakPoincare

/-- **Lemma 6.6 (warm start, [HMRW25, Theorem 4.6]) (corrected: `δ ≥ 0`).**
Hou–Liu–Yu, arXiv:2610.09882, Lemma 6.6, p. 42 (proof pp. 42–43).

Let `P` be a reversible Markov kernel on a finite space, with stationary law `μ` and spectrum in
`[0, 1]`. Suppose `Var_μ[f] ≤ A₀ 𝓔_μ(f, f) + δ osc(f)²` for every `f`, with `A₀ ≥ 1` and `δ ≥ 0`. For
every `B₀`-warm initial law `μinit` and integer `k ≥ 0`,
`d_TV(μinit P^k, μ) ≤ ½ (e^{−k/A₀}(B₀ − 1) + δB₀²)^{1/2}`.

**Formalization Note.** `𝓔_μ(f, f) = ⟨f, (I − P)f⟩_μ` (`fDirichlet`, p. 37). "Spectrum in `[0, 1]`" is
`HasNonnegSpectrum μ P` (`⟨f, Pf⟩_μ ≥ 0`); the upper bound `⟨f, Pf⟩_μ ≤ ⟨f, f⟩_μ` holds for every
reversible stochastic `P`. The hypothesis `δ ≥ 0` is added: the printed statement is false for `δ < 0`
(see the item's differences list). -/
theorem lemma_6_6 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (μ : α → ℝ) (P : Matrix α α ℝ) (A₀ δ B₀ : ℝ) (μinit : α → ℝ) (k : ℕ)
    (hμ : IsLaw μ) (hP : IsStochastic P) (hrev : IsReversible μ P)
    (hspec : HasNonnegSpectrum μ P) (hA : 1 ≤ A₀) (hδ : 0 ≤ δ)
    (hWPI : ∀ f : α → ℝ, fVar μ f ≤ A₀ * fDirichlet μ P f + δ * fOsc f ^ 2)
    (hinit : IsLaw μinit) (hwarm : IsWarm μinit μ B₀) :
    fTV (Matrix.vecMul μinit (P ^ k)) μ ≤
      (1 / 2) * Real.sqrt (Real.exp (-((k : ℝ) / A₀)) * (B₀ - 1) + δ * B₀ ^ 2) := by sorry

end SKWeakPoincare
