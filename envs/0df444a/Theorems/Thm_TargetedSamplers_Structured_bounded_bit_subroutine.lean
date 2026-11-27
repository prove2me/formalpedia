-- Prove2me | Theorems.Thm_TargetedSamplers_Structured_bounded_bit_subroutine
-- name    : TargetedSamplers.Structured.bounded_bit_subroutine
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:00:04.579334+00:00
-- url     : https://prove2.me/theorems/e1a5212b-80e4-5f6d-a41e-835a0e3d2e11
-- title:
--   Bit-cost RAM subroutine calls on random-access input and finite windows of a fair-coin tape
-- statement:
--   Each fixed log-cost RAM returning a single bit has a relocatable native caller block which simulates a fresh invocation on prepared random-access input and a window of the caller's coin tape. Missing host bits count as zero inside that window. The caller's preserved memory may contain arbitrarily large words. If the guest costs T, the native block costs at most a constant times T+1 times the total bit widths of T, input length, coin-window endpoints, epoch and relocation.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, Section 2, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_LogCostRAM_StructuredExecution

open TargetedSamplers TargetedSamplers.Structured

theorem TargetedSamplers.Structured.bounded_bit_subroutine (Q : Program) :
    ∃ (block : Cmd) (C : ℕ), ∀ (pre post : Program) (τ : Tapes) (st : State) (x : List Bool)
      (base len epoch T : ℕ) (v : Bool),
      Q.RunsIn ((⟨x,List.ofFn (fun i : Fin len => τ.coins[base+i.val]?.getD false),[],noOracle⟩ : Tapes)) T (some [v]) →
      st.pc=pre.length → st.halted=false → st.bot=false → st.mem 0=0 → st.mem 10=epoch →
      (∀ i, st.mem (64+4*i) ≤ epoch) → (∀ i<x.length, st.mem (66+4*i)=bitVal x[i]?) →
      st.mem 67=T → st.mem 71=1 → st.mem 75=x.length → st.mem 79=base → st.mem 83=len →
      ∃ steps : ℕ, let P := pre++block.compile pre.length++post
        let u := (P.step τ)^[steps] st
        u.pc=pre.length+block.len ∧ u.halted=false ∧ u.bot=false ∧ u.out=st.out ∧
        u.mem 0=0 ∧ u.mem 10=epoch+1 ∧ (∀ i, u.mem (64+4*i)≤epoch+1) ∧ u.mem 22=v.toNat ∧
        (∀ i, u.mem (66+4*i)=st.mem (66+4*i)) ∧ (∀ i, i≠0 → u.mem (67+4*i)=st.mem (67+4*i)) ∧
        u.work ≤ st.work+C*(T+1)*(1+x.length.size+base.size+len.size+epoch.size+pre.length.size+T.size) := by sorry
