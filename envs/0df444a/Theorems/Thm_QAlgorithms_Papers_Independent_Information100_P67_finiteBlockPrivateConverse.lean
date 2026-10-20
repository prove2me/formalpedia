-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_finiteBlockPrivateConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P67.finiteBlockPrivateConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:01:28.700274+00:00
-- url     : https://prove2.me/theorems/04e6eee0-2dea-47f6-98a5-3552afbd7abb
-- title:
--   Theorem 7.1 (Finite-block private converse)
-- statement:
--   There exist universal constants $C_{\rm app}\ge1$ and $a=1/(4C_{\rm app}^2)>0$ with the following property. Fix a finite-dimensional channel with a symmetric factorization as in Lemma 6.1, let $d=\dim E$, let $q_{\mathcal N}$ be its maximum coherent information, and define $b_{\mathcal N}$ by (6.11)–(6.12). For every valid unassisted collective $(n,M)$ code with $n\ge1$, every $0<\delta<1/2$, and every integer $t$ with $4C_{\rm app}\sqrt n\le t\le n/2$,
--
--   $$f(\mathcal C_n)\le\delta+2e^{-at^2/n}+\left(\sum_{j=0}^t\binom nj\right)^{1/4}\sqrt{\min\left\{1,\frac{2^{nq_{\mathcal N}+b_{\mathcal N}(n,\delta)}d^t}{M}\right\}}.$$
--
--   All dimension constants belong to the fixed channel factorization, and the approximation constants are universal. No entropy inequality or existence of a good filter is assumed as a code hypothesis.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 32, Theorem 7.1 (Finite-block private converse)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Theorem 7.1, PDF p.32. All approximation constants precede the
channel, its symmetric factorization, and the arbitrary collective code. -/
theorem finiteBlockPrivateConverse :
    ∃ Capp : ℝ, 1 ≤ Capp ∧ ∃ a : ℝ, 0 < a ∧ a = 1 / (4 * Capp ^ 2) ∧
    ∀ (A B E F : Type) [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype E] [DecidableEq E] [Nonempty E]
      [Fintype F] [DecidableEq F] [Nonempty F],
    ∀ (U : Matrix (B × E) A ℂ) (V : Matrix (F × E) B ℂ),
      IsSymmetricFactorization U V →
    ∀ n : ℕ, 1 ≤ n → ∀ code : PrivateCode A B n, code.Valid →
    ∀ delta : ℝ, 0 < delta → delta < 1 / 2 → ∀ t : ℕ,
      4 * Capp * Real.sqrt n ≤ (t : ℝ) → (t : ℝ) ≤ (n : ℝ) / 2 →
      optimizedFidelity U code ≤ delta + 2 * Real.exp (-a * (t : ℝ) ^ 2 / n) +
        Real.rpow (binomialVolume n t) (1 / 4 : ℝ) *
          Real.sqrt (min 1 (Real.rpow 2 ((n : ℝ) * maximumCoherentInformation U +
            filterDimensionCorrection (Fintype.card A) (Fintype.card F) n delta) *
              (Fintype.card E : ℝ) ^ t / code.M)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
