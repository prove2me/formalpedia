-- Prove2me | Theorems.Thm_Poly1305DebianCt_relOk_poly1305_finish_v2
-- name    : Poly1305DebianCt.relOk_poly1305_finish_v2
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-26T16:40:50.580752+00:00
-- url     : https://prove2.me/theorems/d2e3e6d9-d00a-5a68-bcd1-d69a3524b71b
-- title:
--   poly1305_finish (Debian libsodium, AArch64) — two-run constant-time contract (v2) in continuation-passing form
-- statement:
--   A relational (two-run) contract (v2: the raw register slot 31 is not compared, so a caller can apply it after another call) of the internal function `poly1305_finish` (text offset 0x420) of `Poly1305DebianCt.lib`, the 4-object library of Debian's libsodium 1.0.22-2 arm64 object code (bundle `Poly1305DebianCt_PlacedObj`), in the leakage model of bundle `Arm64_Leakage`. It is the call rule that the public `crypto_onetimeauth_final`, the one-shot and `crypto_onetimeauth_verify` use for their `bl poly1305_finish`, where the milestone `Poly1305DebianCt.ctInternalOk_poly1305_finish` does not apply: that judgment needs entry states differing only in memory (at these call sites the caller-saved registers hold secret-derived values) and says nothing about the return states.
--
--   For every placement `pl` and hook table `externs` meeting the hypotheses of the judgments of bundle `Poly1305DebianCt_Spec` (`Placeable`, `GuardUniform`, `MemzeroOk`, `MemsetOk`, `Link.PlacedLib.LinkOk`), every pair of stop conditions $stop_1, stop_2$ that agree on any two states with equal `pc`, `sp` and status, and every two states $c_1, c_2$ such that:
--   - $c_1$ is at the address of `poly1305_finish`, $c_2$ has the same `pc` and `sp`, both are running, and the stack pointer is 16-byte aligned;
--   - they agree on the raw register slots 0, 1 and 19–30 (the arguments `x0`, `x1`, the callee-saved registers, the frame pointer and the link register; the raw slot 31, which register reads (`readReg64`) never return, is not compared); the other registers, flags, vector registers and memory may differ;
--   - the code is loaded in both memories;
--   - each memory satisfies `finishPre` for its own ghost value $(st_j, mac_j)$ (96 owned state bytes at `x0` with `leftover` below 16, 16 owned bytes at `x1`, a 4128-byte stack frame) separately from a frame $R_j$ of its own, and the two values agree on `leftover` (`leftoverPub`);
--
--   the two runs from $c_1$ and $c_2$ are observationally equivalent (`Leakage.ObsEquiv`, for the program `lib.program pl externs`, `arity`, $stop_1$, $stop_2$), provided they are observationally equivalent from every pair of states $f_1, f_2$ in which each run $j$ has returned to $c_j$'s link register with $c_j$'s stack pointer and running status (`Returned`), kept the callee-saved registers (`CalleeSavedPreserved`), kept the code loaded, and has memory holding $R_j$ beside 96 bytes at `x0`, 16 bytes at `x1` and the 4128-byte stack frame, with arbitrary contents.
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, libsodium_la-poly1305_donna.o, static function poly1305_finish: two-run (constant-time) contract in continuation-passing form (v2, the raw register slot 31 not compared), the call rule used by crypto_onetimeauth_final, the one-shot and crypto_onetimeauth_verify

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

open Arm64 Arm64.Obj Leakage

theorem relOk_poly1305_finish_v2 :
    ∀ pl : Placement, lib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), Poly1305Libsodium.MemzeroOk externs →
      MemsetOk externs → Link.PlacedLib.LinkOk lib pl externs →
    ∀ stop₁ stop₂ : State → Prop,
      (∀ a b : State, a.pc = b.pc → a.sp = b.sp → a.status = b.status → (stop₁ a ↔ stop₂ b)) →
    ∀ (x₁ x₂ : List (BitVec 8) × List (BitVec 8)) (R₁ R₂ : SepProp) (c₁ c₂ : State),
      c₁.pc = lib.fnAddr pl "poly1305_finish [libsodium_la_poly1305_donna]" →
      c₂.pc = c₁.pc → c₂.sp = c₁.sp →
      c₁.status = .Running → c₂.status = .Running → c₁.spAligned = true →
      (∀ i : BitVec 5, (i.toNat ≤ 1 ∨ (19 ≤ i.toNat ∧ i.toNat ≤ 30)) → c₂.regs.regs i = c₁.regs.regs i) →
      (lib.program pl externs).CodeLoaded c₁.mem → (lib.program pl externs).CodeLoaded c₂.mem →
      (c₁.mem ⊨ finishPre pl x₁ c₁ ∗ R₁) → (c₂.mem ⊨ finishPre pl x₂ c₂ ∗ R₂) →
      leftoverPub x₁ x₂ →
      (∀ f₁ f₂ : State,
        (Returned c₁ f₁ ∧ CalleeSavedPreserved c₁ f₁ ∧ (lib.program pl externs).CodeLoaded f₁.mem ∧
          (f₁.mem ⊨ (memRegion (c₁.readReg64 Reg.x0) 96 ∗ memRegion (c₁.readReg64 Reg.x1) 16 ∗
            stackFrame c₁ 4128) ∗ R₁)) →
        (Returned c₂ f₂ ∧ CalleeSavedPreserved c₂ f₂ ∧ (lib.program pl externs).CodeLoaded f₂.mem ∧
          (f₂.mem ⊨ (memRegion (c₂.readReg64 Reg.x0) 96 ∗ memRegion (c₂.readReg64 Reg.x1) 16 ∗
            stackFrame c₂ 4128) ∗ R₂)) →
        ObsEquiv (lib.program pl externs) arity stop₁ stop₂ f₁ f₂) →
      ObsEquiv (lib.program pl externs) arity stop₁ stop₂ c₁ c₂ := by
  sorry

end Poly1305DebianCt
