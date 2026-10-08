-- Prove2me | Theorems.Thm_SpeedScaling_AVR_lemma_5_8
-- name    : SpeedScaling.AVR.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:29.283638+00:00
-- url     : https://prove2.me/theorems/eaa388c0-8599-4ead-b8f9-dced9e71fe96
-- title:
--   Lemma 5.8 — eigenvalue bound for tree-induced matrices
-- statement:
--   Let $M$ be any tree-induced real matrix and $M^*=(M+M^\mathsf T)/2$. Every eigenvalue of the symmetric matrix $M^*$ is at most two:
--   $$\lambda_{\max}(M^*)\le 2.$$
--
--   This spectral estimate controls the quadratic form arising from canonical A-job instances. It applies to real vectors of either sign.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 381, Lemma 5.8.

import Definitions.Def_SpeedScaling_AVR_TreeInduced

namespace SpeedScaling.AVR

theorem lemma_5_8 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsTreeInduced M)
    (hH : ((1 / 2 : ℝ) • (M + M.transpose)).IsHermitian) :
    ∀ i : Fin n, hH.eigenvalues i ≤ 2 := by sorry

end SpeedScaling.AVR
