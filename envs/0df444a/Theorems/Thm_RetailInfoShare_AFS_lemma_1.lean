-- Prove2me | Theorems.Thm_RetailInfoShare_AFS_lemma_1
-- name    : RetailInfoShare.AFS.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:58.967074+00:00
-- url     : https://prove2.me/theorems/1183a087-66dc-4712-a0ce-05895d0ef94a
-- title:
--   Lemma 1, p. 13 — no sharing: each seller produces a/(2+b(N−1)) and Π_NS = αNa²/[2+b(N−1)]²
-- statement:
--   Assume the standing assumptions and suppose the platform shares no information ($m_{ij} = +\infty$ for all $i,j$). Then an equilibrium exists, and in every equilibrium each seller $i$ produces
--   $$q_{NS,i} = \frac{a}{2 + b(N-1)} \quad \text{almost surely},$$
--   and the platform's expected profit is
--   $$\Pi_{NS} = \frac{\alpha N a^2}{[2 + b(N-1)]^2}.$$
--
--   This is the no-information benchmark against which every sharing strategy is compared.
-- source:
--   Liu, Zhang & Zhang, Information Sharing on Retail Platforms, SSRN 3258109 (PDF of 2023-03-01), p. 13, Lemma 1

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS

theorem lemma_1 (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ) :
    (∃ Q, IsEquilibrium Z (noSharing P.N) Q) ∧
    ∀ Q, IsEquilibrium Z (noSharing P.N) Q →
      (∀ i, Q i =ᵐ[μ] fun _ => qNS P) ∧ platformProfit Z Q = PiNS P := by sorry

end RetailInfoShare.AFS
