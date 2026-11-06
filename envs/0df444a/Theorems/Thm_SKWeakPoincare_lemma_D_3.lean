-- Prove2me | Theorems.Thm_SKWeakPoincare_lemma_D_3
-- name    : SKWeakPoincare.lemma_D_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:41.032426+00:00
-- url     : https://prove2.me/theorems/1a731f94-ce81-4397-a283-ebb5343d1617
-- title:
--   Lemma D.3 — $P_{0,n}((\Omega_n^{\mathrm{end}})^c)\le2e^{-n/4}+2e^{-n/(800\beta_1^2)}$ for all large $n$
-- statement:
--   Let $0<\beta_1<1$ and let $\delta\in(0,1/2)$ satisfy $\delta\log(e/\delta)\le1/(800\beta_1^2)$. Let
--   $$
--   \Omega_n^{\mathrm{end}}=\Big\{A:\ \|A\|_{\mathrm{op}}\le3,\ \max_{|I|\le\delta n}\|\beta_1A_{I,I}\|_{\mathrm{op}}\le\tfrac15\Big\}.
--   $$
--   Then for all sufficiently large $n$,
--   $$
--   P_{0,n}\big((\Omega_n^{\mathrm{end}})^c\big)\le2e^{-n/4}+2e^{-n/(800\beta_1^2)} .
--   $$
--
--   On $\Omega_n^{\mathrm{end}}$ the strong-field estimates of Appendix D give the terminal Poincaré inequality behind Lemma 6.4; the bound $\|A\|_{\mathrm{op}}\le3$ also gives the warmness of consecutive Gibbs laws in Theorem 1.2.
--
--   **Formalization Note** The page fixes $0<\beta_0<\beta_1<1$ and one such $\delta=\delta_{\beta_1}$; $\beta_0$ does not enter $\Omega_n^{\mathrm{end}}$. The outer measure of the complement is bounded, which is the stronger form.
--
--   Differences from the source:
--   - generalization: one δ = δ_{β₁} ∈ (0,1/2) chosen with δ log(e/δ) ≤ 1/(800β₁²) → every δ ∈ (0,1/2) with δ log(e/δ) ≤ 1/(800β₁²); reason: the proof uses only this property; the source's chosen δ is one such δ
--   - encoding: 0 < β₀ < β₁ < 1 fixed → 0 < β₁ < 1; reason: β₀ does not enter Ω_n^end or the bound, and some β₀ ∈ (0,β₁) always exists
--   - encoding: for all sufficiently large n → ∃ N, ∀ n ≥ N; reason: standard
-- source:
--   Hou–Liu–Yu, Simulated annealing and Weak Poincaré inequalities with inverse-polynomial accuracy for the Sherrington–Kirkpatrick model, arXiv:2610.09882, Appendix D.1, p.83 (choice of δ, Ω_n^end, Lemma D.3)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKWeakPoincare_OmegaEnd

open OAI.CriticalSK MeasureTheory

namespace SKWeakPoincare

/-- **Lemma D.3 (the matrix event `Ω_n^end` has overwhelming probability).**
Hou–Liu–Yu, arXiv:2610.09882, Appendix D.1, p. 83 (choice of `δ` and `Ω_n^end`; Lemma D.3).

Fix `0 < β₁ < 1` and `δ ∈ (0, 1/2)` with `δ log(e/δ) ≤ 1/(800β₁²)`, and let
`Ω_n^end = {A : ‖A‖_op ≤ 3, max_{|I|≤δn} ‖β₁A_{I,I}‖_op ≤ 1/5}`. For all sufficiently large `n`,
`P_{0,n}((Ω_n^end)^c) ≤ 2e^{−n/4} + 2e^{−n/(800β₁²)}`.

**Formalization Note.** The page fixes `0 < β₀ < β₁ < 1` and chooses one such `δ = δ_{β₁}`; `β₀` does
not enter `Ω_n^end`, and the statement is made for every `δ` with the stated property (the proof uses
only that property). `P_{0,n} = disorderLaw n`. -/
theorem lemma_D_3 (β₁ δ : ℝ) (hβ0 : 0 < β₁) (hβ1 : β₁ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (hδ : δ * Real.log (Real.exp 1 / δ) ≤ 1 / (800 * β₁ ^ 2)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      disorderLaw n (OmegaEnd β₁ δ n)ᶜ ≤
        ENNReal.ofReal (2 * Real.exp (-((n : ℝ) / 4)) + 2 * Real.exp (-((n : ℝ) / (800 * β₁ ^ 2)))) := by sorry

end SKWeakPoincare
