-- Prove2me | Theorems.Thm_PersuasionNetworks_lemma_4
-- name    : PersuasionNetworks.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:46.880844+00:00
-- url     : https://prove2.me/theorems/85d7d327-abf3-4ce1-b1b0-8dcd856bb9f2
-- title:
--   Lemma 4 — (OPT) has an optimal solution satisfying C1–C4
-- statement:
--   There exists an optimal solution to (OPT) that satisfies C1–C4.
--
--   Together with Theorem 1 this yields the tightness of the relaxation (OPT).
--
--   Differences from the source: none.
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Lemma 4, p.18

import Mathlib
import Definitions.Def_PersuasionNetworks_OPT
import Definitions.Def_PersuasionNetworks_Mechanism

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **Lemma 4**, Candogan, SSRN 3346144 (preprint), p.18 (proof pp.42–48). There exists an optimal solution to (OPT) that
satisfies C1–C4. -/
theorem lemma_4 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r) :
    ∃ p z, IsOptimal μ 𝒯 K b r p z ∧ SatisfiesC μ 𝒯 K p z := by sorry

end PersuasionNetworks
