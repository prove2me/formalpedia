-- Prove2me | Theorems.Thm_RetailInfoShare_AFS_proposition_1_afs
-- name    : RetailInfoShare.AFS.proposition_1_afs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:09.794364+00:00
-- url     : https://prove2.me/theorems/c3ba85b4-9195-4436-8839-26f21bbf3420
-- title:
--   Proposition 1 (AFS half), p. 15 — an optimal AFS strategy never shares partially: every m∗_ij is 0 or +∞
-- statement:
--   Assume the standing assumptions. If $M^*$ is an optimal AFS noise matrix (it is AFS, it has an equilibrium, and no equilibrium of any AFS matrix gives the platform a larger expected profit), then
--   $$m^*_{ij} \in \{0, +\infty\} \qquad \text{for all } i, j.$$
--
--   The platform never adds noise: it either shares a signal truthfully with a seller or withholds it.
--
--   **Formalization Note.** Proposition 1 covers the AFS and AIS formats; only the AFS half is formalized here.
-- source:
--   Liu, Zhang & Zhang, Information Sharing on Retail Platforms, SSRN 3258109 (PDF of 2023-03-01), p. 15, Proposition 1

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS

theorem proposition_1_afs (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (M : NoiseMatrix P.N) (hM : IsOptimalAFS Z M) :
    ∀ i j, M i j = 0 ∨ M i j = ⊤ := by sorry

end RetailInfoShare.AFS
