-- Prove2me | Theorems.Thm_SpeedScaling_AVR_lemma_5_2
-- name    : SpeedScaling.AVR.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:57.113063+00:00
-- url     : https://prove2.me/theorems/89d5483e-8338-4335-9cc1-ece2e0a6f9de
-- title:
--   Lemma 5.2 — preceding A-job integral bound
-- statement:
--   Let $i$ and $j$ be type-A jobs with $i$ preceding $j$ in the paper's A order. For an optimal quadratic schedule,
--   $$\int_{a_j}^{b_j}d_i(t)\,dt\le\int_{a_j}^{b_j}s_i^*(t)\,dt.$$
--
--   This compares the average-rate and executed work of an earlier A-job across a later job's interval.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 378, Lemma 5.2.

import Definitions.Def_SpeedScaling_AVR_Canonical

namespace SpeedScaling.AVR

theorem lemma_5_2 {n : ℕ} (J : Instance n) (S : Schedule n)
    (hS : IsOptimal (fun x : ℝ => x ^ 2) J S) (γ : Fin n → Bool)
    (hγ : IsTyping J S γ) (i j : Fin n) (hi : γ i = true)
    (hj : γ j = true) (hij : precA J S i j) :
    (∫ t in J.a j..J.b j, densityFun J i t) ≤
      (∫ t in J.a j..J.b j, execSpeed S i t) := by sorry

end SpeedScaling.AVR
