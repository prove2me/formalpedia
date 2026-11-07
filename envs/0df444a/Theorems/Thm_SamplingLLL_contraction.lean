-- Prove2me | Theorems.Thm_SamplingLLL_contraction
-- name    : SamplingLLL.contraction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:08.963215+00:00
-- url     : https://prove2.me/theorems/d00f7878-8bac-467f-b379-de6208b661cd
-- title:
--   $M\mathbf 1\le2m_0h$ and the contraction, pp.68–69
-- statement:
--   Under the hypotheses of Theorem 2.6, with $m_0$ the number of constraints, $M\mathbf 1\le2m_0h$, and with $\tilde h=1+16m_0h$,
--   $$
--   M\tilde h\le2m_0h+\frac{32m_0}eh\le\Big(\frac2e+\frac18\Big)\tilde h,\qquad\frac2e+\frac18<1.
--   $$
--   The coordinates of $\tilde h$ lie between $1$ and $1+16m_0$, $\sigma_a\ge3/4$, and the occupation bound is $O(m_0)$ calls for each insertion and $O(m_0^2)$ calls over all insertions, with an absolute constant.
--
--   Differences from the source:
--   - encoding: "$O(m_0)$ calls for each insertion and $O(m_0^2)$ calls over all insertions" → an absolute $C$ with at most $Cm_0$ expected calls for a root insertion from its source law and at most $Cm_0^2$ expected calls of the sampler; reason: the meaning of the $O$ statements
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), proof of Theorem 2.6, pp.68–69

import Mathlib
import Definitions.Def_SamplingLLL_sllAnalysis

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL

open Proc

/-- `M1 ≤ 2m₀h` and the contraction, pp.68–69: with `h̃ = 1 + 16 m₀ h`,
`Mh̃ ≤ 2m₀h + (32m₀/e)h ≤ (2/e + 1/8) h̃`, `2/e + 1/8 < 1`; the coordinates of `h̃` lie between `1` and `1 + 16m₀`;
`σ_a ≥ 3/4`; and the occupation bound is `O(m₀)` calls per insertion and `O(m₀²)` over all insertions, with an
absolute constant.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), proof of Theorem 2.6, pp.68–69. -/
theorem contraction : ∃ C : ℕ, ∀ {n m : ℕ} (I : AtomicCSP n m) (G : Finset (Fin m)) (x : Fin m → ℚ)
    (p : Fin m → ℝ), (∀ a, 0 < x a ∧ x a < 1) → (∀ a, ((I.badProb a : ℚ) : ℝ) ≤ p a) →
    (∀ a ∈ G, I.SamplingGood p a) → I.SLL G p x →
    (∀ (S : Finset (Fin m)) (c : Fin m), c ∉ S →
      let h : ℝ := AtomicCSP.hA x c
      let htilde : Finset (Fin m) × Fin m → ℝ := fun j => 1 + 16 * (m : ℝ) * AtomicCSP.hTask x j
      (∑ j : Finset (Fin m) × Fin m, (I.sllData G x).respM I.ubar (S, c) j) ≤ 2 * (m : ℝ) * h ∧
      (∑ j : Finset (Fin m) × Fin m, (I.sllData G x).respM I.ubar (S, c) j * htilde j) ≤
        2 * (m : ℝ) * h + 32 * (m : ℝ) / Real.exp 1 * h ∧
      2 * (m : ℝ) * h + 32 * (m : ℝ) / Real.exp 1 * h ≤ (2 / Real.exp 1 + 1 / 8) * htilde (S, c) ∧
      (1 : ℝ) ≤ htilde (S, c) ∧ htilde (S, c) ≤ 1 + 16 * (m : ℝ) ∧
      (3 / 4 : ℝ) ≤ AtomicCSP.sigmaA x c) ∧
    (2 / Real.exp 1 + 1 / 8 : ℝ) < 1 ∧
    (∀ i : Fin m,
      ∑ y, ENNReal.ofReal ((I.toCSP.mu (rootSet i) y : ℚ) : ℝ) *
          expCalls (((I.sllData G x).level (fun _ _ => 1) m).insert (rootSet i) i y) ≤
        ((C * m : ℕ) : ℝ≥0∞)) ∧
    expCalls (I.sampler G x) ≤ ((C * m ^ 2 : ℕ) : ℝ≥0∞) := by sorry

end SamplingLLL
