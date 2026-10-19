-- Prove2me | Theorems.Thm_RetailInfoShare_AFS_eq_4
-- name    : RetailInfoShare.AFS.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:00.478491+00:00
-- url     : https://prove2.me/theorems/32b2f133-3a22-4ae7-bca0-d0ebb1802008
-- title:
--   Equation (4), p. 11 — a profile is an equilibrium iff q_i = ½(a − bΣ_{d≠i}E[q_d|y_i] + E[u|y_i]) for every seller
-- statement:
--   Assume the standing assumptions, fix any noise matrix $M$, and let $q = (q_1,\dots,q_N)$ be a profile in which every $q_i$ is admissible (square integrable and measurable with respect to seller $i$'s information $y_i(M)$). Then $q$ is an equilibrium if and only if, for every seller $i$,
--   $$q_i = \frac12\Big(a - b \sum_{d \ne i} E\big[q_d \,\big|\, y_i(M)\big] + E\big[u \,\big|\, y_i(M)\big]\Big) \qquad \text{almost surely.}$$
--
--   This is the first-order condition the paper uses to compute every equilibrium; it turns the Bayesian game into a linear system of conditional expectations.
--
--   **Formalization Note.** The equilibrium is the ex-ante best-response property over all admissible deviations; the statement holds for every noise matrix, not only AFS ones.
-- source:
--   Liu, Zhang & Zhang, Information Sharing on Retail Platforms, SSRN 3258109 (PDF of 2023-03-01), p. 11, Equation (4)

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS

theorem eq_4 (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (M : NoiseMatrix P.N) (Q : Fin P.N → Ω → ℝ) (hQ : ∀ j, IsAdmissible Z M j (Q j)) :
    IsEquilibrium Z M Q ↔
      ∀ i, Q i =ᵐ[μ] fun ω =>
        (P.a - P.b * ∑ d ∈ Finset.univ.erase i, μ[Q d | info Z M i] ω
          + μ[Z.u | info Z M i] ω) / 2 := by sorry

end RetailInfoShare.AFS
