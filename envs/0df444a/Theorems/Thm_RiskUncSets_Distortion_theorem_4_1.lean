-- Prove2me | Theorems.Thm_RiskUncSets_Distortion_theorem_4_1
-- name    : RiskUncSets.Distortion.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:28:38.729981+00:00
-- url     : https://prove2.me/theorems/6759d90a-ec06-4193-9f6b-31e6bcebc760
-- title:
--   Theorem 4.1 (Schmeidler 1986), p. 1488 — a coherent μ is comonotonic iff μ(X) = ∫(−X) dg for a monotone, normalized, submodular g
-- statement:
--   Let $\Omega = \{\omega_1, \dots, \omega_N\}$ and let $\mu : \mathbb R^N \to \mathbb R$ be a coherent risk measure. Then $\mu$ is comonotonic if and only if there is a set function $g : 2^\Omega \to [0, 1]$ that is monotone, normalized and submodular such that
--   $$\mu(X) = \int (-X)\,dg \qquad \text{for all } X \in \mathbb R^N,$$
--   where $\int \cdot\,dg$ is the Choquet integral (3).
--
--   This is Schmeidler's representation of comonotonic coherent risk measures as Choquet integrals with respect to submodular capacities; it is the first step of the proof of Lemma 4.1.
--
--   **Formalization Note** Set functions are real-valued functions on `Set (Fin N)` (here $\mathcal F = 2^\Omega$), with the codomain $[0,1]$ stated as a separate clause. The Choquet integral is the literal formula (3) with Lebesgue integrals over $(-\infty, 0]$ and $(0, \infty)$; on a finite $\Omega$ the integrands are bounded step functions vanishing outside a bounded interval, hence integrable. No probability measure enters the statement.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1488, Theorem 4.1 (Schmeidler 1986); Definitions 4.1–4.3, p. 1487

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

namespace RiskUncSets.Distortion

theorem theorem_4_1 {N : ℕ} (μ : (Fin N → ℝ) → ℝ) (hμ : IsCoherent μ) :
    IsComonotonic μ ↔
      ∃ g : Set (Fin N) → ℝ, (∀ A, g A ∈ Set.Icc (0 : ℝ) 1) ∧ IsMonotoneSF g ∧
        IsNormalizedSF g ∧ IsSubmodularSF g ∧ ∀ X, μ X = choquet g (-X) := by sorry

end RiskUncSets.Distortion
