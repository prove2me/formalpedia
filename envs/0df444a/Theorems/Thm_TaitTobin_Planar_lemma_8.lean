-- Prove2me | Theorems.Thm_TaitTobin_Planar_lemma_8
-- name    : TaitTobin.Planar.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:51.346709+00:00
-- url     : https://prove2.me/theorems/2776d663-34c7-4bec-ba33-9a1f172899f6
-- title:
--   Lemma 8, p. 8 — √(2n − 4) < λ₁ < √(6n) for the planar spectral maximizer
-- statement:
--   Let $n \ge 3$ and let $G$ be a planar graph on $n$ vertices whose spectral radius $\lambda_1 = \lambda_1(G)$ is maximum among all planar graphs on $n$ vertices. Then
--   $$\sqrt{2n-4} < \lambda_1 < \sqrt{6n}.$$
--
--   The lower bound comes from comparison with $K_{2,n-2}$ and the upper bound from the edge count of planar graphs; together they fix the order $\sqrt n$ of $\lambda_1$, which every later estimate of Section 3 uses.
--
--   **Formalization Note** The paper's standing "n large enough" is replaced by the explicit $n \ge 3$, for which the statement holds.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 8, Lemma 8

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- Lemma 8, p. 8: for `n ≥ 3`, a planar graph on `n` vertices of maximum spectral radius has
`√(2n - 4) < λ₁ < √(6n)`. -/
theorem lemma_8 {n : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n)) (hG : TaitTobin.Outerplanar.IsSpecMax IsPlanar G) :
    Real.sqrt (2 * (n : ℝ) - 4) < specRad G ∧ specRad G < Real.sqrt (6 * (n : ℝ)) := by sorry
end TaitTobin.Planar
