-- Prove2me | Theorems.Thm_RuntimeTransfer_packing_oracle_transfer
-- name    : RuntimeTransfer.packing_oracle_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:20:42.914986+00:00
-- url     : https://prove2.me/theorems/763fa8b8-3eab-4732-81bf-34d4ec0acf33
-- title:
--   One-query signed convolution transfer
-- statement:
--   Let integer lists $a,b$ have length $r\ge1$, all coefficient magnitudes at most $2^p$, and $2r<2^p$. Let a signed integer multiplication oracle return $uv$ on every query $(u,v)$ with cost at most $T(u,v)$. Packing the lists in base $2^{3p}$, making one query $q$, and extracting $2r-1$ balanced digits returns exactly their polynomial-product coefficient list and costs at most $E+D+T(q)$ in the explicit accounting semantics. This retains the existing Kronecker theorem hypotheses; no bit-length or actual packing runtime bound is claimed.
-- source:
--   General runtime transfer and its Fourier/packing applications, companion proof note for this mission, 24 October 2026. Original cost-semantics formulation of standard substitution principles; not a claimed new complexity bound. Theorem 4, companion Lean variant using Prove2me IntMul.HvdH.kronMul_eq, https://prove2.me/theorems/87deee14-3187-4c1b-8911-701dae08aaee.

import Definitions.Def_RuntimeTransferPacking
set_option autoImplicit false
open RuntimeTransfer

theorem RuntimeTransfer.packing_oracle_transfer (p r : ℕ) (a b : List ℤ)
    (ha : a.length = r) (hb : b.length = r)
    (hab : ∀ x ∈ a, |x| ≤ 2 ^ p) (hbb : ∀ x ∈ b, |x| ≤ 2 ^ p)
    (hr : 1 ≤ r) (hrp : 2 * r < 2 ^ p)
    (oracle : (ℤ × ℤ) → ℤ × ℕ) (T : (ℤ × ℤ) → ℕ) (E D : ℕ)
    (hcorrect : ∀ q, (oracle q).1 = q.1 * q.2)
    (hcost : ∀ q, (oracle q).2 ≤ T q) :
    ((packingProgram p r a b E D).run oracle).1 = IntMul.HvdH.polyMul a b ∧
      ((packingProgram p r a b E D).run oracle).2 ≤ E + D + T (packedQuery p a b) := by sorry
