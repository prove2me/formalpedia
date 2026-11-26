-- Prove2me | Theorems.Thm_Poly1305DebianApi_donna_verify_reloc_decode
-- name    : Poly1305DebianApi.donna_verify_reloc_decode
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T12:36:41.412415+00:00
-- url     : https://prove2.me/theorems/448f5a8e-289a-427b-b82c-d9c1a8d65511
-- title:
--   poly1305_donna.o, crypto_onetimeauth_poly1305_donna_verify — its relocated instructions decode as the call of crypto_verify_16 and the stack-guard GOT accesses (Debian AArch64 object code)
-- statement:
--   In the four-object library `libsodiumDebianOnetimeauthCtLib` of Debian's libsodium 1.0.22-2 arm64 object code (bundle `Poly1305DebianCt_PlacedObj`), the function `crypto_onetimeauth_poly1305_donna_verify` occupies text offsets 1600–1799. For every placement $\pi$ (base $b$, symbol addresses $\rho$, relaxation flags) under which the library is `Placeable`, the relocated instruction words of that function decode (`Arm64.decode` of `patchedWord`) as follows, with $g = \rho(\texttt{\_\_stack\_chk\_guard})$:
--
--   - **the call at offset 1744** decodes to `bl` with displacement $(b + 1868) - (b + 1744)$, a call of `crypto_verify_16` (text offset 1868);
--   - **the two stack-guard GOT accesses**, `adrp xN, :got:__stack_chk_guard; ldr xN, [xN, :got_lo12:__stack_chk_guard]` at offsets $k = 1608$ with $N = 4$ and $k = 1748$ with $N = 1$, decode in each of the linker's three shapes:
--     - if $\mathrm{relax}(k)$: `nop` at $k$, and `adr xN` with displacement $g - (b + k + 4)$ at $k + 4$;
--     - if not $\mathrm{relax}(k)$: `adrp xN` with displacement $\mathrm{page}(g) - \mathrm{page}(b + k)$ at $k$ (`pageOf` clears the low 12 bits);
--     - if not $\mathrm{relax}(k)$ but $\mathrm{relax}(k + 4)$: `add xN, xN, #lo12(g)` at $k + 4$;
--     - if neither: `ldr xN, [xN, #(g & 0xfff)]` (64-bit, unsigned offset) at $k + 4$.
--
--   This is an auxiliary step of the proof of `Poly1305DebianApi.verifyOk_donna_verify` (the contract of `crypto_onetimeauth_poly1305_donna_verify` in the mission on this object code), stated on its own so that its proof can be checked separately: the whole proof was too slow for one verifier run.
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, poly1305_donna.o, crypto_onetimeauth_poly1305_donna_verify: the decoded relocated instructions (an auxiliary step of Poly1305DebianApi.verifyOk_donna_verify)

import Definitions.Def_Poly1305DebianCt_PlacedObj

open Arm64 Arm64.Obj

namespace Poly1305DebianApi

theorem donna_verify_reloc_decode (pl : Placement)
    (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl) :
    decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl 1744) =
        some (.bl (pl.base + BitVec.ofNat 64 1868 - (pl.base + BitVec.ofNat 64 1744))) ∧
      ∀ (off : Nat) (n : BitVec 5), (off = 1608 ∧ n = 4#5) ∨ (off = 1748 ∧ n = 1#5) →
        (pl.relax off = true →
          decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off) = some .nop ∧
          decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.adr false (.gpr n)
              (pl.ρ "__stack_chk_guard" - (pl.base + BitVec.ofNat 64 (off + 4))))) ∧
        (pl.relax off = false →
          decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off) =
            some (.adr true (.gpr n)
              (pageOf (pl.ρ "__stack_chk_guard") - pageOf (pl.base + BitVec.ofNat 64 off)))) ∧
        (pl.relax off = false → pl.relax (off + 4) = true →
          decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.addSubImm .W64 .ADD (.gpr n) (.gpr n)
              ((pl.ρ "__stack_chk_guard").extractLsb' 0 12) false)) ∧
        (pl.relax off = false → pl.relax (off + 4) = false →
          decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.ldr .W64 .X64 false (.gpr n)
              (.Offset (.gpr n) (pl.ρ "__stack_chk_guard" &&& 0xfff#64)))) := by
  sorry

end Poly1305DebianApi
