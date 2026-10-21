-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_gammaL_mono
-- name    : TestDistancing.Equilibrium.gammaL_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:16.406057+00:00
-- url     : https://prove2.me/theorems/d30d75d9-9d06-4a4b-8cee-b59447b79d45
-- title:
--   Proof of Theorem 1(b) — low-type mixing rises with testing
-- statement:
--   For sufficiently large populations and policies $\alpha\le\alpha'$ in the interior of $A_2$, let $g,g'\in[0,1]$ solve the low-type indifference equation (9) at $\alpha,\alpha'$ respectively. Then
--
--   $$g\le g'.$$
--
--   This is the monotonicity of low-type activity used in the non-monotone infection result. **Formalization Note** The large-population and interior qualifications match the setting of Theorem 1(b), where the source invokes this claim.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, pp. 37–38 (PDF 39–40), proof of Theorem 1(b), after (9)

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

theorem gammaL_mono (P : Params) (hP : P.Standing) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n →
      ∀ α α' : ℝ × ℝ, α ∈ interior (A2 P n) → α' ∈ interior (A2 P n) →
      PolicyLe α α' → ∀ g g' : ℝ,
      (∀ l : Fin n, ¬ IsHigh P l →
        PinfMix P (g, 1) α l 1 = (1 : ℝ) / n + P.vL) →
      (∀ l : Fin n, ¬ IsHigh P l →
        PinfMix P (g', 1) α' l 1 = (1 : ℝ) / n + P.vL) →
      g ∈ Set.Icc (0 : ℝ) 1 → g' ∈ Set.Icc (0 : ℝ) 1 → g ≤ g' := by sorry

end TestDistancing.Equilibrium
