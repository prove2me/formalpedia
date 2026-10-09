-- Prove2me | Theorems.Thm_WassVarReg_Boundary_lemma_EC_5
-- name    : WassVarReg.Boundary.lemma_EC_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:48.291135+00:00
-- url     : https://prove2.me/theorems/d36806f6-fda3-42a1-8d6a-d541ddb1c4ca
-- title:
--   Lemma EC.5, p. ec4 — w.p. ≥ 1 − e^{−t}, E_{P_n}[h] ≤ E_P[h] + 2E_⊗[ℜ_n(H)] + M√(t/2n) for all h ∈ H ⊆ [0, M]
-- statement:
--   Let $(\mathcal Z, d)$ be a metric space with its Borel $\sigma$-algebra and $P_{\rm true}$ a probability measure on it. Let $z_1, \dots, z_n$ ($n \ge 1$) be an i.i.d. sample from $P_{\rm true}$ with empirical law $P_n$. Let $\mathcal H$ be a set of measurable functions $h : \mathcal Z \to [0, M]$, $M \ge 0$, and let $t > 0$. Then with probability at least $1 - e^{-t}$, for every $h \in \mathcal H$,
--   $$\mathbb E_{P_n}[h] \le \mathbb E_{P_{\rm true}}[h] + 2\,\mathbb E_\otimes[\mathfrak R_n(\mathcal H)] + M\sqrt{\frac{t}{2n}}.$$
--
--   This is the uniform deviation bound, adapted from Shalev-Shwartz and Ben-David's Theorem 26.5, that the paper applies to the classes of indicators of neighbourhoods of the non-smooth sets $\mathcal D_f$.
--
--   **Formalization Note**
--   1. The page prints the deviation term as $M\sqrt{2t/n}$; the proof (McDiarmid's inequality with bounded differences $M/n$) gives $M\sqrt{t/(2n)}$, the constant Lemma EC.11 and Theorem 1(III) use. The sharper constant is stated.
--   2. The $\mathfrak R_n(\mathcal H)$ of the printed statement is the expected Rademacher complexity $\mathbb E_\otimes[\mathfrak R_n(\mathcal H)]$, as the proof's symmetrization step shows.
--   3. The probability is the product measure of the set of samples on which some $h$ violates the bound (an outer measure; the quantifier over $\mathcal H$ is inside the event).
--   4. Added technical hypotheses, implicit in the paper: each $h$ is measurable (so that $\mathbb E_{P_{\rm true}}[h]$ is a genuine integral), and $\mathcal H$ is Rademacher-measurable at sample size $n$ (the uniform deviation, the empirical Rademacher complexity and the double-sample deviation are measurable; true for countable $\mathcal H$).
--   5. The lemma's second inequality ($\mathbb E_{P_{\rm true}}[h] \le \mathbb E_{P_n}[h] + \dots$) is not used in the paper and is not stated here.
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), Lemma EC.5, first inequality, p. ec4 (constant from its proof)

import Mathlib
import Definitions.Def_WassVarReg_Boundary_Setting

open MeasureTheory Filter Topology
open scoped ENNReal

namespace WassVarReg.Boundary

/-- Lemma EC.5, first inequality, p. ec4, with the constant `M √(t/(2n))` that its proof
(McDiarmid) gives; the page prints `M √(2t/n)`. `ℜ_n(H)` is `E_⊗[ℜ_n(H)]`, as in the proof. -/
theorem lemma_EC_5 {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (Ptrue : ProbabilityMeasure Z) (n : ℕ) (hn : 0 < n)
    (H : Set (Z → ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hH : ∀ h ∈ H, Measurable h ∧ ∀ z, 0 ≤ h z ∧ h z ≤ M)
    (hmeas : RademacherMeasurable n Ptrue H)
    (t : ℝ) (ht : 0 < t) :
    MinimaxWass.DataDep.sampleLaw n Ptrue
      {ω | ¬ ∀ h ∈ H, (1 / (n : ℝ)) * ∑ i : Fin n, h (ω i) ≤
        (∫ z, h z ∂(Ptrue : Measure Z)) + 2 * rademacher n Ptrue H +
          M * Real.sqrt (t / (2 * n))} ≤
      ENNReal.ofReal (Real.exp (-t)) := by sorry

end WassVarReg.Boundary
