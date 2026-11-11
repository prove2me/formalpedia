-- Prove2me | Theorems.Thm_ShamirLLR_eq_2
-- name    : ShamirLLR.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:57.36805+00:00
-- url     : https://prove2.me/theorems/0a50da1c-b73e-48b4-a55d-02cbda315de3
-- title:
--   Eq. (2) — $\mathrm{Insec}(a;d)\le 2\Delta(a;d)$
-- statement:
--   Let $p$ be an odd prime, $1\le d<m$, and $a\in\mathcal A_{p,m}$ an ordered tuple of distinct nonzero evaluation places. Then
--   $$
--   \mathrm{Insec}(a;d)\le2\,\Delta(a;d).
--   $$
--
--   A bound on Reed–Solomon pseudorandomness therefore gives a leakage-resilience bound for Shamir sharing, for every fixed $a$.
--
--   Differences from the source:
--   - encoding: one-bit leakage $f_i:\mathbb F_p\to\{0,1\}$ → `ZMod p → Bool`; reason: same functions
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Eq. (2), p.3 (PDF p.4); standing assumption $1\le d<m$, p.1

import Mathlib
import Definitions.Def_ShamirLLR_evalTuples
import Definitions.Def_ShamirLLR_deltaClass
import Definitions.Def_ShamirLLR_insec

set_option autoImplicit false

namespace ShamirLLR

/-- **Eq. (2).** For every tuple `a` of distinct nonzero evaluation places and `1 ≤ d < m`,
`Insec(a; d) ≤ 2 Δ(a; d)`.

Source: Hwang–Maji–Shkredov–Ye, *Local Leakage Resilience of Multiplication-friendly Shamir
Secret Sharing*, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…), Eq. (2), p.3.

**Formalization Note.** "Odd prime" is `[Fact p.Prime]` with `p ≠ 2`; `1 ≤ d < m` is the
standing assumption of p.1; `a ∈ A_{p,m}`. -/
theorem eq_2 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m d : ℕ) (hd : 1 ≤ d) (hdm : d < m)
    (a : Fin m → ZMod p) (ha : a ∈ evalTuples p m) :
    insec a d ≤ 2 * delta a d := by sorry

end ShamirLLR
