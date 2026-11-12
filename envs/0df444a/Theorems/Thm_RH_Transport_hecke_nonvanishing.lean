-- Prove2me | Theorems.Thm_RH_Transport_hecke_nonvanishing
-- name    : RH.Transport.hecke_nonvanishing
-- status  : Open
-- author  : @0xbf
-- created : 2026-11-11T16:16:03.488377+00:00
-- url     : https://prove2.me/theorems/f22369c4-e4f3-4220-845d-680f0c43a966
-- title:
--   Hecke-family zero-freeness at the refined boundary
-- statement:
--   Let $B=4374785349/5000000000$. For every character in the source's Hecke family over $\mathbb Q(\sqrt{-3})$, its Hecke $L$-function has no zero when $\operatorname{Re}(s)>B$, apart from the possible pole of the trivial character at $s=1$.
--
--   This is the analytic zero-free input in the LW56e2 refinement; the next step transfers it to Dirichlet $L$-functions.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/Nonvanishing.lean, declaration RH.Transport.hecke_nonvanishing: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Nonvanishing.lean

import Mathlib
import Definitions.Def_HeckeSevenEighths
open OAI.SevenEighths

theorem RH.Transport.hecke_nonvanishing
    (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : (4374785349 / 5000000000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by sorry
