-- Prove2me | Theorems.Thm_SpeedScaling_AVR_lemma_5_1
-- name    : SpeedScaling.AVR.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:54.524823+00:00
-- url     : https://prove2.me/theorems/514d497f-870d-40af-b3d4-dacf09326e61
-- title:
--   Lemma 5.1 — bitonicity reduction
-- statement:
--   Given a candidate instance $(J,S)$ optimized by the quadratic schedule speed $s^*$, there is another candidate instance $(J',S')$ using the same speed profile and time window in which every job is type A or B, while
--   $$\operatorname{AVR}(J')=\operatorname{AVR}(J).$$
--
--   This reduction permits the separate A/B analysis. Jobs may be split, so the new finite job count can differ.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 378, Lemma 5.1.

import Definitions.Def_SpeedScaling_AVR_Canonical

namespace SpeedScaling.AVR

theorem lemma_5_1 {n : ℕ} (J : Instance n) (S : Schedule n)
    (hS : IsOptimal (fun x : ℝ => x ^ 2) J S) :
    ∃ (n' : ℕ) (J' : Instance n') (job' : ℝ → Option (Fin n')),
      J'.t0 = J.t0 ∧ J'.t1 = J.t1 ∧
      IsOptimal (fun x : ℝ => x ^ 2) J' ⟨S.s, job'⟩ ∧
      (∃ γ : Fin n' → Bool, IsTyping J' ⟨S.s, job'⟩ γ) ∧
      AVR J' = AVR J := by sorry

end SpeedScaling.AVR
