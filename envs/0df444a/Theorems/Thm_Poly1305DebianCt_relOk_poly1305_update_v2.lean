-- Prove2me | Theorems.Thm_Poly1305DebianCt_relOk_poly1305_update_v2
-- name    : Poly1305DebianCt.relOk_poly1305_update_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T16:40:50.608801+00:00
-- url     : https://prove2.me/theorems/1270c552-191f-5602-8bae-36bd11e74db9
-- title:
--   poly1305_update (Debian libsodium, AArch64) — two-run constant-time contract (v2) in continuation-passing form
-- statement:
--   A relational (two-run) contract (v2: the raw register slot 31 is not compared, so a caller can apply it after another call) of the internal function `poly1305_update` (text offset 0x2b0) of `Poly1305DebianCt.lib`, the 4-object library of Debian's libsodium 1.0.22-2 arm64 object code (bundle `Poly1305DebianCt_PlacedObj`), in the leakage model of bundle `Arm64_Leakage`. It is the call rule that the public `crypto_onetimeauth_update`, the one-shot and `crypto_onetimeauth_verify` use for their `bl poly1305_update`, where the milestone `Poly1305DebianCt.ctInternalOk_poly1305_update` does not apply: that judgment needs entry states differing only in memory (at these call sites the caller-saved registers hold secret-derived values) and says nothing about the return states.
--
--   For every placement `pl` and hook table `externs` meeting the hypotheses of the judgments of bundle `Poly1305DebianCt_Spec` (`Placeable`, `GuardUniform`, `MemzeroOk`, `MemsetOk`, `Link.PlacedLib.LinkOk`), every pair of stop conditions $stop_1, stop_2$ that agree on any two states with equal `pc`, `sp` and status, and every two states $c_1, c_2$ such that:
--   - $c_1$ is at the address of `poly1305_update`, $c_2$ has the same `pc` and `sp`, both are running, and the stack pointer is 16-byte aligned;
--   - they agree on the raw register slots 0, 1, 2 and 19–30 (the arguments `x0`–`x2`, the callee-saved registers, the frame pointer and the link register; the raw slot 31, which register reads (`readReg64`) never return, is not compared); the other registers, flags, vector registers and memory may differ;
--   - the code is loaded in both memories;
--   - each memory satisfies `updateIntPre` for its own ghost value $(ro_j, st_j, m_j)$ (96 owned state bytes at `x0` with `leftover` $L_j$ below 16, the message bytes $m_j$ at `x1`, owned or read-only by $ro_j$, with `x2` $= |m_j|$, a 32-byte stack frame) separately from a frame $R_j$ of its own, and the two values agree on $ro$ and on `leftover` (`updatePub`);
--
--   the two runs from $c_1$ and $c_2$ are observationally equivalent (`Leakage.ObsEquiv`, for the program `lib.program pl externs`, `arity`, $stop_1$, $stop_2$), provided they are observationally equivalent from every pair of states $f_1, f_2$ in which each run $j$ has returned to $c_j$'s link register with $c_j$'s stack pointer and running status (`Returned`), kept the callee-saved registers (`CalleeSavedPreserved`) and `x0`, kept the code loaded, and has memory holding $R_j$ beside 96 state bytes at `x0` whose `leftover` is $(L_j + |m_j|) \bmod 16$, $|m_j|$ bytes at `x1` (owned or read-only by $ro_j$), and the 32-byte stack frame.
--
--   The kept `x0` reflects GCC's interprocedural register allocation: the one-shot calls `poly1305_finish` right after `poly1305_update` relying on `x0` being unchanged. The `leftover` on return is what lets a later `poly1305_finish` in both runs see equal public data.
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, libsodium_la-poly1305_donna.o, static function poly1305_update: two-run (constant-time) contract in continuation-passing form (v2, the raw register slot 31 not compared), the call rule used by crypto_onetimeauth_update, the one-shot and crypto_onetimeauth_verify

import Definitions.Def_Poly1305DebianCt_Spec

namespace Poly1305DebianCt

open Arm64 Arm64.Obj Leakage

theorem relOk_poly1305_update_v2 :
    ∀ pl : Placement, lib.Placeable pl → GuardUniform pl →
    ∀ externs : String → Option (State → State), Poly1305Libsodium.MemzeroOk externs →
      MemsetOk externs → Link.PlacedLib.LinkOk lib pl externs →
    ∀ stop₁ stop₂ : State → Prop,
      (∀ a b : State, a.pc = b.pc → a.sp = b.sp → a.status = b.status → (stop₁ a ↔ stop₂ b)) →
    ∀ (x₁ x₂ : Bool × List (BitVec 8) × List (BitVec 8)) (R₁ R₂ : SepProp) (c₁ c₂ : State),
      c₁.pc = lib.fnAddr pl "poly1305_update [libsodium_la_poly1305_donna]" →
      c₂.pc = c₁.pc → c₂.sp = c₁.sp →
      c₁.status = .Running → c₂.status = .Running → c₁.spAligned = true →
      (∀ i : BitVec 5, (i.toNat ≤ 2 ∨ (19 ≤ i.toNat ∧ i.toNat ≤ 30)) → c₂.regs.regs i = c₁.regs.regs i) →
      (lib.program pl externs).CodeLoaded c₁.mem → (lib.program pl externs).CodeLoaded c₂.mem →
      (c₁.mem ⊨ updateIntPre pl x₁ c₁ ∗ R₁) → (c₂.mem ⊨ updateIntPre pl x₂ c₂ ∗ R₂) →
      updatePub x₁ x₂ →
      (∀ f₁ f₂ : State,
        (Returned c₁ f₁ ∧ CalleeSavedPreserved c₁ f₁ ∧ f₁.readReg64 Reg.x0 = c₁.readReg64 Reg.x0 ∧
          (lib.program pl externs).CodeLoaded f₁.mem ∧
          (f₁.mem ⊨ ((∃∗ st' : List (BitVec 8),
              ⌜st'.length = 96 ∧ Poly1305Libsodium.u64At st' 64 =
                (Poly1305Libsodium.u64At x₁.2.1 64 + x₁.2.2.length) % 16⌝ ∗
              (c₁.readReg64 Reg.x0 ↦ₛ st')) ∗
            (∃∗ m' : List (BitVec 8), ⌜m'.length = x₁.2.2.length⌝ ∗
              Poly1305Libsodium.bytesIn x₁.1 (c₁.readReg64 Reg.x1) m') ∗
            stackFrame c₁ 32) ∗ R₁)) →
        (Returned c₂ f₂ ∧ CalleeSavedPreserved c₂ f₂ ∧ f₂.readReg64 Reg.x0 = c₂.readReg64 Reg.x0 ∧
          (lib.program pl externs).CodeLoaded f₂.mem ∧
          (f₂.mem ⊨ ((∃∗ st' : List (BitVec 8),
              ⌜st'.length = 96 ∧ Poly1305Libsodium.u64At st' 64 =
                (Poly1305Libsodium.u64At x₂.2.1 64 + x₂.2.2.length) % 16⌝ ∗
              (c₂.readReg64 Reg.x0 ↦ₛ st')) ∗
            (∃∗ m' : List (BitVec 8), ⌜m'.length = x₂.2.2.length⌝ ∗
              Poly1305Libsodium.bytesIn x₂.1 (c₂.readReg64 Reg.x1) m') ∗
            stackFrame c₂ 32) ∗ R₂)) →
        ObsEquiv (lib.program pl externs) arity stop₁ stop₂ f₁ f₂) →
      ObsEquiv (lib.program pl externs) arity stop₁ stop₂ c₁ c₂ := by
  sorry

end Poly1305DebianCt
