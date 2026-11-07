-- Prove2me | Theorems.Thm_SigmoidWire_lemma_4_5
-- name    : SigmoidWire.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:19.251507+00:00
-- url     : https://prove2.me/theorems/361d4fcb-9650-4a77-ba1a-5a2dee0894e2
-- title:
--   Lemma 4.5: rational approximation of Sigmoid with degree $O(\ln^2(a/\varepsilon))$
-- statement:
--   There is a constant $C_0$ such that for every $a\ge1$ and $\varepsilon\in(0,1/2]$ there is a rational function $r$ of degree at most $C_0\ln^2(a/\varepsilon)$, with no pole in $[-a,a]$, such that
--
--   $$
--   |r(x)-\mathrm{Sigmoid}(x)|\le\varepsilon\qquad\text{for every }x\in[-a,a].
--   $$
--
--   This is what makes the lower-bound machinery of Theorem 4.4 applicable to sigmoid gates.
--
--   Differences from the source:
--   - encoding: a rational function r with no pole in [−a, a] → polynomials P, Q of natDegree ≤ C₀·ln²(a/ε) with Q ≠ 0 on [−a, a]; reason: degree of P/Q is max{deg P, deg Q} (p.19)
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Lemma 4.5, p.20 (restated p.60)

import Mathlib
import Definitions.Def_SigmoidWire_RatApproxOn

namespace SigmoidWire

/-- **Lemma 4.5 (rational approximation of Sigmoid).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Lemma 4.5, p.20 (PDF p.22),
restated p.60: "There is a constant C₀ such that for every a ≥ 1 and ε ∈ (0, 1/2], there is a
rational function r of degree at most C₀ ln²(a/ε), with no pole in [−a, a], such that
|r(x) − Sigmoid(x)| ≤ ε for every x ∈ [−a, a]."

**Formalization Note.** `Sigmoid` is Mathlib's `Real.sigmoid`; `RatApproxOn` asks for real
polynomials `P, Q` of degree at most the bound with `Q ≠ 0` on `[−a, a]`. On this domain
`ln(a/ε) ≥ ln 2 > 0`. -/
theorem lemma_4_5 :
    ∃ C₀ : ℝ, ∀ a : ℝ, 1 ≤ a → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      RatApproxOn Real.sigmoid a (C₀ * Real.log (a / ε) ^ 2) ε := by sorry

end SigmoidWire
