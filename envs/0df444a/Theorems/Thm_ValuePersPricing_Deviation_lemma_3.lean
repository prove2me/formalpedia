-- Prove2me | Theorems.Thm_ValuePersPricing_Deviation_lemma_3
-- name    : ValuePersPricing.Deviation.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:28.438861+00:00
-- url     : https://prove2.me/theorems/3ca53bfe-1e94-46af-aa70-4dd0ad35f86c
-- title:
--   Lemma 3, p. 14 — D = ∫_M^{S+M−1} F̄(µx + c)dx = ∫_0^M 1 − F̄(µx + c)dx
-- statement:
--   Let $(F,c)$ be a market with mean $\mu>0$ and margin $M=1-c/\mu\in[0,1]$, and let $D=\mathbb E|V-\mu|/(2\mu)$ be its coefficient of deviation. Then
--   $$D=\int_0^M\big(1-\bar F(\mu x+c)\big)\,dx,$$
--   and if $F$ has scale $S$ then also
--   $$D=\int_M^{S+M-1}\bar F(\mu x+c)\,dx .$$
--
--   These are the two integral representations of $D$ (equation (8)) on which the proof of Theorem 2 is built: the low and high regimes bound the cCDF inside the second, the medium regime inside the first.
--
--   Differences from the source:
--   - generalization: both identities for F with scale S → the identity D = ∫_0^M 1 − F̄(µx + c)dx is stated for every law, with no scale hypothesis; reason: its proof (p. ec5) does not use S, and the unbounded-support case of Theorem 2 needs it; with a scale it is the printed statement.
--   - encoding: F with margin M (µ > 0 implicit) → hypotheses Market ν c and 0 < µ; reason: D = E|V − µ|/(2µ) is undefined at µ = 0; every margin M ∈ [0, 1] is covered, including the degenerate M = 0; standing assumptions of §2 as Market ν c.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), p. 14 (PDF 14), Lemma 3, Eq. (8); proof p. ec5 (PDF 37)

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- Lemma 3 (p. 14), equation (8): the two integral representations of `D`,
`D = ∫_M^{S+M−1} F̄(µx + c) dx` (for a law of scale `S`) and `D = ∫_0^M (1 − F̄(µx + c)) dx`
(for every law, bounded or not). Margin `M ∈ [0, 1]`: the degenerate case `M = 0` (`c = µ`) is
included. -/
theorem lemma_3 (ν : Measure ℝ) (c : ℝ) (hm : Market ν c) (hμ : 0 < mean ν) :
    (∀ S : ℝ, IsScale ν S →
      coefDev ν = ∫ x in (margin ν c)..(S + margin ν c - 1), tail ν (mean ν * x + c)) ∧
    coefDev ν = ∫ x in (0 : ℝ)..(margin ν c), (1 - tail ν (mean ν * x + c)) := by sorry

end ValuePersPricing.Deviation
