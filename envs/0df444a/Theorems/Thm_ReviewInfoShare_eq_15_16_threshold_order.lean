-- Prove2me | Theorems.Thm_ReviewInfoShare_eq_15_16_threshold_order
-- name    : ReviewInfoShare.eq_15_16_threshold_order
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:24.386698+00:00
-- url     : https://prove2.me/theorems/d1ad6948-3344-42be-b0c0-40c1c0223be3
-- title:
--   (15)–(16) — order of the thresholds (corrected: (15) off the range $\Psi^0_i\le\bar q^2-\underline q^2\le\Psi^\infty_i$)
-- statement:
--   The quality-gap threshold rises with reviews,
--   $$
--   \Psi^0_i<\Psi^\infty_i,
--   $$
--   and if $\pi(\bar q)<\pi(\underline q)$ and $\bar q^2-\underline q^2$ lies outside $[\Psi^0_i,\Psi^\infty_i]$, so does the signal threshold,
--   $$
--   \Phi^0_i<\Phi^\infty_i .
--   $$
--   Information sharing can be arranged only under more restrictive conditions with reviews than without. The case that matters for the thresholds is $\bar q^2-\underline q^2>\Psi^\infty_i$, where both denominators are positive.
--
--   Differences from the source:
--   - correction: Φ⁰ᵢ < Φ^∞ᵢ, with no condition on q̄² − q̲² → Φ⁰ᵢ < Φ^∞ᵢ when q̄² − q̲² > Ψ^∞ᵢ or q̄² − q̲² < Ψ⁰ᵢ, under π(q̄) < π(q̲); reason: the printed inequality is false for Ψ⁰ᵢ < q̄² − q̲² < Ψ^∞ᵢ (at α = 10, μ_θ = 2, σ_θ = σ_p = 1, q̲ = 1, q̄ = 5/4, c̲ = 1, c̄ = 2 one has Φ⁰ᵢ = 1032/11 > 0 > Φ^∞ᵢ) and has a zero denominator at the two endpoints
--   - generalization: (16) under π(q̄) < π(q̲), assumed throughout the paper (p.16) → (16) without that hypothesis; reason: Ψ⁰ᵢ and Ψ^∞ᵢ do not involve π, so the statement specializes to the printed setting
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, (15)–(16), p.20

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Thresholds

namespace ReviewInfoShare

/-- Shin–Zeevi, SSRN 3886954, (15)–(16), p.20: `Ψ⁰ᵢ < Ψ^∞ᵢ`, and `Φ⁰ᵢ < Φ^∞ᵢ` when `q̄² − q̲²` lies
outside `[Ψ⁰ᵢ, Ψ^∞ᵢ]`.

**Formalization Note.** (15) is corrected: as printed it has no condition on `q̄² − q̲²`. It fails for
`Ψ⁰ᵢ < q̄² − q̲² < Ψ^∞ᵢ`, where `Φ⁰ᵢ > 0 > Φ^∞ᵢ`, and a denominator is zero at the two endpoints. For
`q̄² − q̲² < Ψ⁰ᵢ` both denominators are negative and the inequality still holds. -/
theorem eq_15_16_threshold_order (P : Params) (hP : P.Admissible) :
    P.psiI0 < P.psiIInf ∧
    (P.pi .high < P.pi .low →
      (P.psiIInf < P.qH ^ 2 - P.qL ^ 2 ∨ P.qH ^ 2 - P.qL ^ 2 < P.psiI0) → P.phiI0 < P.phiIInf) := by sorry

end ReviewInfoShare
