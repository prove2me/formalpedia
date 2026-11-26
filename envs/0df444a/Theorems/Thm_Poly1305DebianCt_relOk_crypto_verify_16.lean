-- Prove2me | Theorems.Thm_Poly1305DebianCt_relOk_crypto_verify_16
-- name    : Poly1305DebianCt.relOk_crypto_verify_16
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T19:41:02.591826+00:00
-- url     : https://prove2.me/theorems/1c5dc771-8b02-4cff-99bc-73648d98f223
-- title:
--   crypto_verify_16 (Debian libsodium, AArch64) — two-run constant-time contract in continuation-passing form
-- statement:
--   A relational (two-run) contract of `crypto_verify_16` (text offset 0x74c) of `Poly1305DebianCt.lib`, the 4-object library of Debian's libsodium 1.0.22-2 arm64 object code (bundle `Poly1305DebianCt_PlacedObj`), in the leakage model of bundle `Arm64_Leakage`. It is the call rule that `crypto_onetimeauth_verify` uses for its `bl crypto_verify_16`, where the milestone `Poly1305DebianCt.ctPublicOk_crypto_verify_16_32_64` does not apply: that judgment needs entry states differing only in memory (at that call site the caller-saved registers hold what the `sodium_memzero` hook left) and says nothing about the return states.
--
--   For every placement `pl` and hook table `externs` meeting the hypotheses of the judgments of bundle `Poly1305DebianCt_Spec` (`Placeable`, `GuardUniform`, `MemzeroOk`, `MemsetOk`, `Link.PlacedLib.LinkOk`), every pair of stop conditions $stop_1, stop_2$ that agree on any two states with equal `pc`, `sp` and status, and every two states $c_1, c_2$ such that:
--   - $c_1$ is at the address of `crypto_verify_16`, $c_2$ has the same `pc` and `sp`, both are running, and the stack pointer is 16-byte aligned;
--   - they agree on the raw register slots 0, 1 and 19–30 (the arguments `x0`, `x1`, the callee-saved registers, the frame pointer and the link register); the other registers, flags, vector registers and memory may differ;
--   - the code is loaded in both memories;
--   - each memory satisfies `verifyNPre 16` for its own ghost value $(roX_j, roY_j, a_j, b_j)$ (16 bytes $a_j$ at `x0` and 16 bytes $b_j$ at `x1`, each owned or read-only, and a 32-byte stack frame) together with the library's data objects in their initial state (`lib.dataInit pl`, which holds the `optblocker_u16` the function reads), separately from a frame $R_j$ of its own, and the two values agree on $roX$ and $roY$ (`verifyNPub`);
--
--   the two runs from $c_1$ and $c_2$ are observationally equivalent (`Leakage.ObsEquiv`, for the program `lib.program pl externs`, `arity`, $stop_1$, $stop_2$), provided they are observationally equivalent from every pair of states $f_1, f_2$ in which each run $j$ has returned to $c_j$'s link register with $c_j$'s stack pointer and running status (`Returned`), kept the callee-saved registers (`CalleeSavedPreserved`), kept the code loaded, and has memory holding $R_j$ beside the unchanged inputs $a_j$, $b_j$, the 32-byte stack frame and the data objects in their initial state. The result in `w0` may differ between the runs.
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, libsodium_la-verify.o, crypto_verify_16: two-run (constant-time) contract in continuation-passing form, the call rule used by crypto_onetimeauth_verify

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

open Arm64 Arm64.Obj Leakage

theorem relOk_crypto_verify_16 :
    ∀ pl : Placement, lib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), Poly1305Libsodium.MemzeroOk externs →
      MemsetOk externs → Link.PlacedLib.LinkOk lib pl externs →
    ∀ stop₁ stop₂ : State → Prop,
      (∀ a b : State, a.pc = b.pc → a.sp = b.sp → a.status = b.status → (stop₁ a ↔ stop₂ b)) →
    ∀ (x₁ x₂ : Bool × Bool × List (BitVec 8) × List (BitVec 8)) (R₁ R₂ : SepProp) (c₁ c₂ : State),
      c₁.pc = lib.fnAddr pl "crypto_verify_16" →
      c₂.pc = c₁.pc → c₂.sp = c₁.sp →
      c₁.status = .Running → c₂.status = .Running → c₁.spAligned = true →
      (∀ i : BitVec 5, (i.toNat ≤ 1 ∨ (19 ≤ i.toNat ∧ i.toNat ≤ 30)) → c₂.regs.regs i = c₁.regs.regs i) →
      (lib.program pl externs).CodeLoaded c₁.mem → (lib.program pl externs).CodeLoaded c₂.mem →
      (c₁.mem ⊨ (verifyNPre 16 pl x₁ c₁ ∗ lib.dataInit pl) ∗ R₁) →
      (c₂.mem ⊨ (verifyNPre 16 pl x₂ c₂ ∗ lib.dataInit pl) ∗ R₂) →
      verifyNPub x₁ x₂ →
      (∀ f₁ f₂ : State,
        (Returned c₁ f₁ ∧ CalleeSavedPreserved c₁ f₁ ∧ (lib.program pl externs).CodeLoaded f₁.mem ∧
          (f₁.mem ⊨ (Poly1305Libsodium.bytesIn x₁.1 (c₁.readReg64 Reg.x0) x₁.2.2.1 ∗
            Poly1305Libsodium.bytesIn x₁.2.1 (c₁.readReg64 Reg.x1) x₁.2.2.2 ∗ stackFrame c₁ 32 ∗
            lib.dataInit pl) ∗ R₁)) →
        (Returned c₂ f₂ ∧ CalleeSavedPreserved c₂ f₂ ∧ (lib.program pl externs).CodeLoaded f₂.mem ∧
          (f₂.mem ⊨ (Poly1305Libsodium.bytesIn x₂.1 (c₂.readReg64 Reg.x0) x₂.2.2.1 ∗
            Poly1305Libsodium.bytesIn x₂.2.1 (c₂.readReg64 Reg.x1) x₂.2.2.2 ∗ stackFrame c₂ 32 ∗
            lib.dataInit pl) ∗ R₂)) →
        ObsEquiv (lib.program pl externs) arity stop₁ stop₂ f₁ f₂) →
      ObsEquiv (lib.program pl externs) arity stop₁ stop₂ c₁ c₂ := by
  sorry

end Poly1305DebianCt
