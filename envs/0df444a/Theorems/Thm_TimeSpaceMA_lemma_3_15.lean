-- Prove2me | Theorems.Thm_TimeSpaceMA_lemma_3_15
-- name    : TimeSpaceMA.lemma_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:12.358034+00:00
-- url     : https://prove2.me/theorems/4b0f1c66-1d42-44f7-8774-2ad5a6cd1828
-- title:
--   Lemma 3.15 = Theorem A.4 — lines detect distance
-- statement:
--   Let $G$ be a systematic subset-sum code with the distance of Lemma 3.10(b), $r\ge1$, and $Y$ a word on $[L]^r$ with entries in $\mathbb Q^d$. If the line test rejects $Y$ with probability $\eta$, then
--   $$\mathrm{dist}(Y,G^{\otimes r})\le\kappa_r\,\eta,\qquad\kappa_r:=4(2r)^8\delta^{-7r}.$$
--
--   Differences from the source:
--   - generalization: G the code of Lemma 3.10 → any systematic subset-sum code with q ≥ 2 and the distance of Lemma 3.10(b); reason: the proof on pp.36–37 uses only nonempty supports, that distance and systematic positions, and the code of Lemma 3.10 has them
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Lemma 3.15, p.13; Theorem A.4, p.36

import Definitions.Def_TimeSpaceMA_tensorEncode

namespace TimeSpaceMA

/-- **Lemma 3.15 = Theorem A.4** (Lines detect distance; Williams, Xi, STOC 2027 submission, manuscript
sha256 184c2f95…, pp.13, 36). For a word `Y` on `[L]^r` with entries in `ℚ^d`, if the line test rejects `Y`
with probability `η` then `dist(Y, G^{⊗r}) ≤ κ_r η`, `κ_r := 4 (2r)^8 δ^{−7r}`.

**Formalization Note** `G` is any systematic subset-sum code with the distance of Lemma 3.10(b) and `q ≥ 2`;
the proof uses only nonempty supports, systematic positions and that distance. `η` is the exact fraction of
rejected points. -/
theorem lemma_3_15 {q L : ℕ} (hq : 2 ≤ q) (G : SubsetSumCode q L) (σ : Fin q → Fin L)
    (hσ : G.IsSystematic σ) (hG : G.HasGroupDistance) (r d : ℕ) (hr : 1 ≤ r)
    (Y : (Fin r → Fin L) → Fin d → ℚ) :
    distToTensor G Y ≤ kappa G.delta r * lineTestReject G Y := by sorry

end TimeSpaceMA
