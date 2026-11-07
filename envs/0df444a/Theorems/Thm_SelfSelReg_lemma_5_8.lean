-- Prove2me | Theorems.Thm_SelfSelReg_lemma_5_8
-- name    : SelfSelReg.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:26.420428+00:00
-- url     : https://prove2.me/theorems/72dba613-e238-4ccd-8436-279420b22dc3
-- title:
--   Lemma 5.8 — even-moment weight bounds $\mathbb P(T\le Y_i\le T+1)\le\lambda_i^{(2r)}$ and $e^{-T^2}\le\lambda_i^{(2r)}\le e^{4r\log K-T^2/(3K)}$
-- statement:
--   In the Gaussian self-selection model ($n\ge1$, $2\le k\le n$) under Assumption 1.2 with constants $B\ge1$, $\Delta\in(0,1]$, let $K=16(1+B^2)^3/\Delta^4$, let $s\ge1$ be an integer and $T>0$ with $T^2\ge Ks$. For every $i\in[k]$ and $1\le r\le s$,
--   $$\mathbb P(T\le Y_i\le T+1)\le\lambda_i^{(2r)}\le e^{4r\log K+T^2/(2K^4)}\,\mathbb P(T\le Y_i\le T+1),$$
--   and consequently
--   $$e^{-T^2}\le\lambda_i^{(2r)}\le e^{4r\log K-T^2/(3K)} .$$
--   Here $\lambda_i^{(2r)}=a_{2r}(\sigma_i^2)\|w_i\|_2^{2r}$ is the degree-$2r$ weight.
--
--   The weights are thus comparable to the slice probabilities, which lets the error terms of Theorem 5.1(i) be measured against the total weight.
--
--   **Formalization Note** Natural logarithm; $T$ and $s$ are free, as on the page.
--
--   Differences from the source:
--   - encoding: λ_i^{(2r)}, with T implicit → weight w T i r, with T an explicit argument; reason: the weight depends on T; T is the lemma's own free threshold
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Lemma 5.8, (31)–(32), p.23 (PDF p.26)

import Mathlib
import Definitions.Def_SelfSelReg_jointLaw
import Definitions.Def_SelfSelReg_SatisfiesAssumption
import Definitions.Def_SelfSelReg_hypK
import Definitions.Def_SelfSelReg_restrictedMoment

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Lemma 5.8** (Even-Moment Weight Bounds).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Lemma 5.8, p.23 (PDF p.26): "Consider the Gaussian self-selection model
(Definition 1.1) under the boundedness and uncoveredness assumptions (Assumption 1.2). Use the choice
of K from Hyperparameters 4.1. Let s ≥ 1 be an integer and suppose T > 0 and T² ≥ Ks. For every
i ∈ [k] and 1 ≤ r ≤ s, P(T ≤ Y_i ≤ T + 1) ≤ λ_i^{(2r)} ≤ e^{4r log K + T²/(2K⁴)} P(T ≤ Y_i ≤ T + 1).
(31) Consequently, e^{−T²} ≤ λ_i^{(2r)} ≤ e^{4r log K − T²/(3K)}." (32)

**Formalization Note.** `K = hypK B ∆`; `s`, `T` free, as on the page. `λ_i^{(2r)}` is `weight w T i r`
(18); `P(T ≤ Y_i ≤ T + 1)` is the `jointLaw` measure of the slice of `Y_i`. Natural logarithm. -/
theorem lemma_5_8 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (B Δ : ℝ) (hB : 1 ≤ B)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (w : Fin k → EuclideanSpace ℝ (Fin n))
    (hw : SatisfiesAssumption B Δ w) (s : ℕ) (hs : 1 ≤ s) (T : ℝ) (hT : 0 < T)
    (hTs : hypK B Δ * s ≤ T ^ 2) (i : Fin k) (r : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) :
    (jointLaw n k).real {z | T ≤ response w z.1 z.2 i ∧ response w z.1 z.2 i ≤ T + 1} ≤
        weight w T i r ∧
      weight w T i r ≤ Real.exp (4 * r * Real.log (hypK B Δ) + T ^ 2 / (2 * hypK B Δ ^ 4)) *
        (jointLaw n k).real {z | T ≤ response w z.1 z.2 i ∧ response w z.1 z.2 i ≤ T + 1} ∧
      Real.exp (-T ^ 2) ≤ weight w T i r ∧
      weight w T i r ≤ Real.exp (4 * r * Real.log (hypK B Δ) - T ^ 2 / (3 * hypK B Δ)) := by sorry

end SelfSelReg
