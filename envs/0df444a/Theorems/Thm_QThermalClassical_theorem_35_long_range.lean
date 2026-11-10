-- Prove2me | Theorems.Thm_QThermalClassical_theorem_35_long_range
-- name    : QThermalClassical.theorem_35_long_range
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:28.925114+00:00
-- url     : https://prove2.me/theorems/6f639007-1541-4f84-9a1a-e4304269a327
-- title:
--   Theorem 35, long-range bullet — the witness is $(s,k)$-long-range
-- statement:
--   For every integer $k\ge2$ and every $s>0$, setting $m=\lfloor k/2\rfloor+1$, $a=s/2$ and $J_{x,y}=0$ in the Hamiltonian (408) of Theorem 35 results in an $(s,k)$-long-range Pauli Hamiltonian, on every lattice $\Lambda_L=\{1,\dots,L\}^D$.
--
--   Its terms $-\tfrac s2Q_{x,i}$ have weight $2(m-1)\le k$ and every data qubit lies in exactly two of them.
--
--   Differences from the source:
--   - encoding: $k\ge2$ → a natural number $k\ge2$; reason: $k$ is a locality; for real $k\ge2$ the $(s,k)$-long-range class equals the $(s,\lfloor k\rfloor)$ class and $\lfloor\lfloor k\rfloor/2\rfloor=\lfloor k/2\rfloor$
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, long-range bullet, first sentence, p.84

import Mathlib
import Definitions.Def_QThermalClassical_IsLongRangePauli
import Definitions.Def_QThermalClassical_ent35Coeff

set_option autoImplicit false

namespace QThermalClassical

/-- **Theorem 35, long-range bullet, first sentence.** For every `k ≥ 2` and `s > 0`, setting
`m = ⌊k/2⌋ + 1`, `a = s/2` and `J_{x,y} = 0` in (408) results in an `(s, k)`-long-range Pauli
Hamiltonian.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 35, long-range bullet, p.84.

**Formalization Note.** `k` is a natural number (a locality); for a real `k ≥ 2` the class of
`(s, k)`-long-range Hamiltonians equals that for `⌊k⌋` and `⌊⌊k⌋/2⌋ = ⌊k/2⌋`. `k / 2` is
natural-number division, i.e. `⌊k/2⌋`. The statement holds for every lattice `D, L`. -/
theorem theorem_35_long_range (D L : ℕ) (k : ℕ) (hk : 2 ≤ k) (s : ℝ) (hs : 0 < s) :
    IsLongRangePauli s (k : ℝ) (ent35Coeff D L (k / 2 + 1) (s / 2) (fun _ _ => 0)) := by sorry

end QThermalClassical
