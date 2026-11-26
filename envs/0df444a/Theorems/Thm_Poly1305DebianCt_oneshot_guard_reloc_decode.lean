-- Prove2me | Theorems.Thm_Poly1305DebianCt_oneshot_guard_reloc_decode
-- name    : Poly1305DebianCt.oneshot_guard_reloc_decode
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-26T20:30:06.728444+00:00
-- url     : https://prove2.me/theorems/aa37b9c6-ecf9-410c-8de3-1912fff78277
-- title:
--   crypto_onetimeauth_poly1305_donna (Debian libsodium, AArch64) — its two stack-guard GOT accesses decode in each linker shape
-- statement:
--   For every placement `pl` under which `libsodiumDebianOnetimeauthCtLib` (bundle `Poly1305DebianCt_PlacedObj`: Debian's libsodium 1.0.22-2 arm64 objects of `crypto_onetimeauth`, `onetimeauth_poly1305`, `poly1305_donna` and `verify`, unmodified) is `Placeable`, the relocated instruction words of the two GOT accesses to `__stack_chk_guard` in the donna one-shot `crypto_onetimeauth_poly1305_donna` — at text offsets 1420/1424 with register `x4` and 1544/1548 with `x0` — decode as follows, where $k$ is the offset, $n$ the register and $g$ the placed address of `__stack_chk_guard`:
--   - if the linker relaxed the pair (`pl.relax k`): `nop` at $k$, and `adr xn` with displacement $g - (b + k + 4)$ at $k + 4$;
--   - otherwise `adrp xn` with page displacement $\mathrm{page}(g) - \mathrm{page}(b + k)$ at $k$, and at $k + 4$ either `add xn, xn, #lo12(g)` (if `pl.relax (k + 4)`) or `ldr xn, [xn, #(g & 0xfff)]`.
--
--   Here $b$ is `pl.base`. This is the counterpart, for the one-shot, of the published `Poly1305DebianApi.donna_verify_reloc_decode` (the verify function's two sites, 1608 and 1748); it lets proofs about the one-shot import the decoding instead of re-checking it.
-- source:
--   Debian libsodium 1.0.22-2 (arm64), libsodium-dev_1.0.22-2_arm64.deb (https://deb.debian.org/debian/pool/main/libs/libsodium/libsodium-dev_1.0.22-2_arm64.deb), libsodium.a, libsodium_la-poly1305_donna.o, crypto_onetimeauth_poly1305_donna: decoding of its two stack-guard GOT accesses (text offsets 1420 and 1544) in each linker shape

import Definitions.Def_Poly1305DebianCt_PlacedObj

open Arm64 Arm64.Obj

namespace Poly1305DebianCt

theorem oneshot_guard_reloc_decode (pl : Placement)
    (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl) :
      ∀ (off : Nat) (n : BitVec 5), (off = 1420 ∧ n = 4#5) ∨ (off = 1544 ∧ n = 0#5) →
        (pl.relax off = true →
          decode (libsodiumDebianOnetimeauthCtText.patchedWord pl off) = some .nop ∧
          decode (libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.adr false (.gpr n)
              (pl.ρ "__stack_chk_guard" - (pl.base + BitVec.ofNat 64 (off + 4))))) ∧
        (pl.relax off = false →
          decode (libsodiumDebianOnetimeauthCtText.patchedWord pl off) =
            some (.adr true (.gpr n)
              (pageOf (pl.ρ "__stack_chk_guard") - pageOf (pl.base + BitVec.ofNat 64 off)))) ∧
        (pl.relax off = false → pl.relax (off + 4) = true →
          decode (libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.addSubImm .W64 .ADD (.gpr n) (.gpr n)
              ((pl.ρ "__stack_chk_guard").extractLsb' 0 12) false)) ∧
        (pl.relax off = false → pl.relax (off + 4) = false →
          decode (libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.ldr .W64 .X64 false (.gpr n)
              (.Offset (.gpr n) (pl.ρ "__stack_chk_guard" &&& 0xfff#64)))) := by
  sorry

end Poly1305DebianCt
