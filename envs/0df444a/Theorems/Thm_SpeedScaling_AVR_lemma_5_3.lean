-- Prove2me | Theorems.Thm_SpeedScaling_AVR_lemma_5_3
-- name    : SpeedScaling.AVR.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:56.311702+00:00
-- url     : https://prove2.me/theorems/57307717-db12-40bd-993a-318ae8bc7d3e
-- title:
--   Lemma 5.3 — nonpreemption reduction
-- statement:
--   For a bitonic candidate instance optimized by speed $s^*$, there is another bitonic candidate instance using the same speed profile and time window in which each job has one execution interval and
--   $$F_A(J')\ge F_A(J).$$
--
--   The job count may change because a preempted job can be split. This reduces maximization of $F_A$ to nonpreemptive instances.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 379, Lemma 5.3.

import Definitions.Def_SpeedScaling_AVR_Canonical

namespace SpeedScaling.AVR

theorem lemma_5_3 {n : ℕ} (J : Instance n) (S : Schedule n)
    (hS : IsOptimal (fun x : ℝ => x ^ 2) J S) (γ : Fin n → Bool)
    (hγ : IsTyping J S γ) :
    ∃ (n' : ℕ) (J' : Instance n') (job' : ℝ → Option (Fin n'))
      (γ' : Fin n' → Bool),
      J'.t0 = J.t0 ∧ J'.t1 = J.t1 ∧
      IsOptimal (fun x : ℝ => x ^ 2) J' ⟨S.s, job'⟩ ∧
      IsTyping J' ⟨S.s, job'⟩ γ' ∧
      IsNonPreemptive J' ⟨S.s, job'⟩ ∧
      fA J S γ ≤ fA J' ⟨S.s, job'⟩ γ' := by sorry

end SpeedScaling.AVR
