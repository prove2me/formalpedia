-- Prove2me | Theorems.Thm_QuasilinearAG_Encoding_lemma_4_3
-- name    : QuasilinearAG.Encoding.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:41:52.153252+00:00
-- url     : https://prove2.me/theorems/21afc9ba-1b24-48be-b710-aad4e80576ee
-- title:
--   Lemma 4.3 — the public root arena is linear: $\kappa Q_*\le 2D$
-- statement:
--   For all $q\ge3$ and $h\ge1$, with $\kappa=\lceil\log_q h\rceil+1$, $Q_*=q^\kappa$ and $D=q^h$ as in (3.2), one has $\kappa Q_*\le2D$.
--
--   Differences from the source:
--   none.
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 16, Lemma 4.3 (PDF p. 18)

import Mathlib
import Definitions.Def_QuasilinearAG_Encoding_Tower

namespace QuasilinearAG.Encoding

/-- Lemma 4.3 (The public root arena is linear), p. 16 (PDF 18). For all `q ≥ 3` and `h ≥ 1`, with
`κ = ⌈log_q h⌉ + 1`, `Q* = q^κ` and `D = q^h` as in (3.2), one has `κ Q* ≤ 2D`. -/
theorem lemma_4_3 (q h : ℕ) (hq : 3 ≤ q) (hh : 1 ≤ h) :
    kappaOf q h * q ^ kappaOf q h ≤ 2 * q ^ h := by sorry

end QuasilinearAG.Encoding
