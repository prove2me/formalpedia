-- Prove2me | Theorems.Thm_Poly1305Boringssl_internalOk_poly1305_update
-- name    : Poly1305Boringssl.internalOk_poly1305_update
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-24T10:06:28.799562+00:00
-- url     : https://prove2.me/theorems/436605d3-2e7a-4230-898c-b8d5a7b9a650
-- title:
--   poly1305.cc, poly1305_update — the block routine runs RFC 8439's loop mod 2^130 − 5
-- statement:
--   Total correctness of the internal function `poly1305_update` (C++ symbol `_ZN12_GLOBAL__N_115poly1305_updateEPNS_17poly1305_state_stEPKhm`) in the AArch64 object code of BoringSSL's `poly1305.cc` (`boringsslPoly1305Lib`), under the contract `blocksSpec`, for every placement of the library the linker could produce. The function is a symbol of the code block, though not exported. For every ghost value $(st, m)$, every frame $R$ and every entry state at the function with the stack pointer 16-byte aligned whose memory satisfies the precondition separately from $R$, execution terminates and returns to the caller with the stack pointer and the callee-saved registers restored, $R$ untouched and the postcondition holding; it never panics, exits or runs out of memory.
--   - **Before:** `x0` points to the 56 owned bytes $st$ of the state's limbs with `StateOk` $st$; the bytes $m$ are readable at `x1`; `x2` $= |m|$ (any length); the caller lends the 16 bytes below the stack pointer.
--   - **After:** `x0` points to 56 bytes $st'$ with `StateOk` $st'$ and the same first 36 bytes (the limbs $r_0, \dots, r_4$, $s_1, \dots, s_4$), whose accumulator satisfies `limbVal (hLimb st')` $\equiv$ `accumulate (limbVal (rLimb st)) (limbVal (hLimb st)) m` $\pmod{2^{130} - 5}$: RFC 8439's loop over the 16-byte blocks of $m$, the last one possibly shorter, run with $r$ the value of the $r$ limbs from the old accumulator. $m$ and the stack frame are handed back.
--
--   poly1305.cc, lines 53–55: “poly1305_blocks updates \`state\` given some amount of input data. This function may only be called with a \`len\` that is not a multiple of 16 at the end of the data. Otherwise the input must be buffered into 16 byte blocks.”
-- source:
--   BoringSSL commit f8b3e2347647a6ad8d26e2ce4cee34f792d5f880 (https://boringssl.googlesource.com/boringssl/+/f8b3e2347647a6ad8d26e2ce4cee34f792d5f880), crypto/poly1305/poly1305.cc lines 53–148 (the internal poly1305_update)

import Definitions.Def_Poly1305Boringssl_Spec

namespace Poly1305Boringssl

theorem internalOk_poly1305_update :
    internalOk
      "_ZN12_GLOBAL__N_115poly1305_updateEPNS_17poly1305_state_stEPKhm [boringssl_poly1305]"
      (fun _ => blocksSpec) := by
  sorry

end Poly1305Boringssl
