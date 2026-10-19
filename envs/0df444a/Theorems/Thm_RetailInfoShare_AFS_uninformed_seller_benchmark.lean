-- Prove2me | Theorems.Thm_RetailInfoShare_AFS_uninformed_seller_benchmark
-- name    : RetailInfoShare.AFS.uninformed_seller_benchmark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:01.849296+00:00
-- url     : https://prove2.me/theorems/92e38609-678f-4705-870b-375a102ccf5d
-- title:
--   §3.1, p. 13 — a seller who receives no information earns exactly his no-sharing expected profit
-- statement:
--   Assume the standing assumptions. Let $M$ be any noise matrix, $q$ an equilibrium under $M$, and $q^0$ an equilibrium under no sharing. If seller $j$ receives nothing under $M$ ($m_{ij} = +\infty$ for every $i$), then
--   $$\pi_j(q) = \pi_j(q^0).$$
--
--   Sharing information with some sellers therefore never affects the expected profit of the sellers left out.
-- source:
--   Liu, Zhang & Zhang, Information Sharing on Retail Platforms, SSRN 3258109 (PDF of 2023-03-01), §3.1, p. 13, 'It is worth mentioning that the sellers who do not receive information will always have the same expected profit …'

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS

theorem uninformed_seller_benchmark (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (M : NoiseMatrix P.N) (Q Q₀ : Fin P.N → Ω → ℝ) (hQ : IsEquilibrium Z M Q)
    (hQ₀ : IsEquilibrium Z (noSharing P.N) Q₀) (j : Fin P.N) (hj : ∀ i, M i j = ⊤) :
    sellerProfit Z Q j = sellerProfit Z Q₀ j := by sorry

end RetailInfoShare.AFS
