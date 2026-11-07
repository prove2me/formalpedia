-- Prove2me | Theorems.Thm_PrivBayesTest_lemma_2_4
-- name    : PrivBayesTest.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:25:11.17463+00:00
-- url     : https://prove2.me/theorems/cb7b6dd5-4805-4455-8fa9-54e25b206c41
-- title:
--   Lemma 2.4 (= Theorem 1.4): $\inf_{R,S}F_\alpha(R,S)=\sup_{\|\varphi\|_\infty\le\tilde\alpha\varepsilon/2}G_\alpha(\varphi)$
-- statement:
--   Let $P,Q$ be probability measures on $\mathcal X$, $\alpha\in(0,1)$, $\varepsilon>0$ and $\tilde\alpha=\min(\alpha,1-\alpha)$. Then
--
--   $$
--   \inf_{R,S\in\Delta(\mathcal X)^2}\alpha\mathrm{KL}(R\|P)+(1-\alpha)\mathrm{KL}(S\|Q)+\tilde\alpha\varepsilon\mathrm{TV}(R,S)
--   \;=\;\sup_{\|\varphi\|_\infty\le\tilde\alpha\varepsilon/2}\Big\{-\alpha\log\int e^{-\varphi/\alpha}dP-(1-\alpha)\log\int e^{\varphi/(1-\alpha)}dQ\Big\},
--   $$
--
--   the supremum over measurable $\varphi:\mathcal X\to\mathbb R$ with $|\varphi(x)|\le\tilde\alpha\varepsilon/2$ for all $x$.
--
--   This dual representation is the source of the optimal private test: its optimizer is a clipped log-likelihood ratio (Proposition 2.5).
--
--   Differences from the source:
--   - encoding: ‖φ‖∞ ≤ α̃ε/2 → measurable φ with |φ(x)| ≤ α̃ε/2 for every x; reason: the objective depends on φ only (P+Q)-almost everywhere, so an essential bound gives the same supremum
--   - encoding: real-valued exponents, divergences and suprema → extended reals (EReal/ENNReal) with −log 0 = +∞; reason: Lean convention; avoids junk values of real sup/inf; same instances
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Lemma 2.4, p.10 (= Theorem 1.4, p.6)

import Mathlib
import Definitions.Def_PrivBayesTest_klTvValue
import Definitions.Def_PrivBayesTest_dualObj

open MeasureTheory

namespace PrivBayesTest

/-- **Lemma 2.4** (= Theorem 1.4, p.6) of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.10. Fix probability measures `P, Q` on `X` and
`α ∈ (0,1)`. Then for any `ε > 0`,
`inf_{R,S∈Δ(X)²} α KL(R ∥ P) + (1 − α) KL(S ∥ Q) + α̃ ε TV(R, S)
  = sup_{‖φ‖∞ ≤ α̃ε/2} {−α log ∫ e^{−φ/α} dP − (1 − α) log ∫ e^{φ/(1−α)} dQ}`.

**Formalization Note** Both sides in `EReal`. The supremum ranges over measurable `φ : X → ℝ` with
`|φ(x)| ≤ α̃ε/2` for every `x` (the objective depends on `φ` only `(P+Q)`-almost everywhere, so an
essential bound gives the same supremum). The objective is `PrivBayesTest.dualObj`. -/
theorem lemma_2_4 {X : Type*} [MeasurableSpace X] (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ((klTvInf ε P Q α : ENNReal) : EReal) =
      ⨆ (φ : X → ℝ) (_ : Measurable φ) (_ : ∀ x, |φ x| ≤ alphaTilde α * ε / 2),
        dualObj P Q α φ := by sorry

end PrivBayesTest
