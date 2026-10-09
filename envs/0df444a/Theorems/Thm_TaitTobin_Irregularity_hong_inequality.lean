-- Prove2me | Theorems.Thm_TaitTobin_Irregularity_hong_inequality
-- name    : TaitTobin.Irregularity.hong_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:52.25943+00:00
-- url     : https://prove2.me/theorems/c5734591-86e5-48e5-84d0-db37b6c72fc5
-- title:
--   Hong's inequality (cited [37], p. 14) — λ₁² ≤ 2e(G) − (n − 1) for connected G
-- statement:
--   Let $G$ be a connected graph on $n$ vertices with $e(G)$ edges and spectral radius $\lambda_1$ (the largest eigenvalue of its adjacency matrix). Then
--   $$\lambda_1^2 \le 2e(G) - (n-1).$$
--
--   This is Hong's 1988 bound, which the paper cites and uses twice in Section 4: to show that a maximizer of $\lambda_1 - d$ has $\lambda_1 \approx n/2$ (Lemma 16) and to control the degrees around the vertex of maximum eigenvector entry (Lemma 17).
--
--   **Formalization Note** Hong proves the bound for graphs without isolated vertices; it is stated here for connected graphs, which is how the paper uses it. For $n = 1$ both sides are $0$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 14, proof of Lemma 16 (citing Y. Hong, J. Math. Res. Exposition 8 (1988), [37])

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

namespace TaitTobin.Irregularity

open Classical WangKangXue.SpectralTuran

/-- Hong's inequality (Hong 1988, cited as [37] on p. 14): a connected graph on `n` vertices with
`e(G)` edges satisfies `λ₁² ≤ 2e(G) − (n − 1)`. -/
theorem hong_inequality {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    specRad G ^ 2 ≤ 2 * (G.edgeFinset.card : ℝ) - ((n : ℝ) - 1) := by sorry
end TaitTobin.Irregularity
