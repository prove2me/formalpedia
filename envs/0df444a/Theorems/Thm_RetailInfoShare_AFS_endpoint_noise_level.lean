-- Prove2me | Theorems.Thm_RetailInfoShare_AFS_endpoint_noise_level
-- name    : RetailInfoShare.AFS.endpoint_noise_level
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:03.872228+00:00
-- url     : https://prove2.me/theorems/5b363af4-027a-4b93-99fe-ada773f0c819
-- title:
--   §4, p. 16 — under AFS an interior noise level for one seller is strictly beaten by noise level 0 or +∞
-- statement:
--   Assume the standing assumptions. Let $M$ be an AFS noise matrix and $j$ a seller, and write $M[j \mapsto \eta]$ for $M$ with seller $j$'s common noise level replaced by $\eta \in [0,+\infty]$. If $0 < \eta < +\infty$ and $q$ is an equilibrium under $M[j\mapsto\eta]$, then there are $\eta' \in \{0, +\infty\}$ and an equilibrium $q'$ under $M[j \mapsto \eta']$ with
--   $$\Pi(q) < \Pi(q').$$
--
--   In words: with the other sellers' noise levels held fixed, the platform's profit as a function of one seller's noise level is maximized only at the endpoints, so the platform shares truthfully with a seller or not at all. This is the paper's explanation of Proposition 1.
--
--   **Formalization Note.** The sentence on p. 16 covers both the AFS and AIS formats; only the AFS half is formalized. "The optimal noise level is either 0 or $+\infty$" is read strictly: an interior level is beaten by one of the endpoints.
-- source:
--   Liu, Zhang & Zhang, Information Sharing on Retail Platforms, SSRN 3258109 (PDF of 2023-03-01), §4, p. 16, 'Hence the optimal noise level for any seller under the AFS or AIS formats is either 0 or +∞ …'

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS

theorem endpoint_noise_level (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (M : NoiseMatrix P.N) (hM : IsAFS M) (j : Fin P.N) (η : ℝ≥0∞) (hη0 : η ≠ 0) (hηtop : η ≠ ⊤)
    (Q : Fin P.N → Ω → ℝ) (hQ : IsEquilibrium Z (setColumn M j η) Q) :
    ∃ η' : ℝ≥0∞, (η' = 0 ∨ η' = ⊤) ∧ ∃ Q' : Fin P.N → Ω → ℝ,
      IsEquilibrium Z (setColumn M j η') Q' ∧ platformProfit Z Q < platformProfit Z Q' := by sorry

end RetailInfoShare.AFS
