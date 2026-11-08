-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_42
-- name    : SpencerEight.lemma_8_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:55.281198+00:00
-- url     : https://prove2.me/theorems/19bb203a-0b87-41b6-b99c-5485756d0f0c
-- title:
--   Lemma 8.42 — refined coding amplitude
-- statement:
--   Put $s_+:=0.674489750196$, $a:=0.635553145368$ and $b:=(1-2s_+a)/s_+^2$. The conclusions of Lemmas 8.2 and 8.3 hold with $s_+$ in place of $s_\star$, using the same density family with these parameters.
--
--   The final signing uses this larger amplitude only.
--
--   Differences from the source:
--   - encoding: the conclusions of Lemmas 8.2 and 8.3 → the predicates PeakedDensityComparison and LosslessPartialSigning at the refined parameters, with the inequality for E := q²/2; reason: the same statements as in lemma_8_2 and lemma_8_3
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.42, p.104 (PDF p.104)

import Mathlib
import Definitions.Def_SpencerEight_PeakedDensityComparison
import Definitions.Def_SpencerEight_LosslessPartialSigning
import Definitions.Def_SpencerEight_sPlus
import Definitions.Def_SpencerEight_aPlus

namespace SpencerEight

/-- Lemma 8.42 (Refined coding amplitude), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.104 (PDF p.104). The conclusions of Lemmas 8.2 and 8.3 with `s₊` in place of `s⋆`, `a := 0.635553145368`, `b := (1 − 2s₊a)/s₊²`. -/
theorem lemma_8_42 :
    PeakedDensityComparison sPlus aPlus ∧ LosslessPartialSigning sPlus ∧
    (∀ q : ℝ, 0 < q → q < 1 → Real.binEntropy ((1 - q) / 2) < Real.log 2 - q ^ 2 / 2) := by sorry

end SpencerEight
