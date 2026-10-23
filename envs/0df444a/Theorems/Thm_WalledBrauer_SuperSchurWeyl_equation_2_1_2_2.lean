-- Prove2me | Theorems.Thm_WalledBrauer_SuperSchurWeyl_equation_2_1_2_2
-- name    : WalledBrauer.SuperSchurWeyl.equation_2_1_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:23.72989+00:00
-- url     : https://prove2.me/theorems/832e3ea6-b3b9-4c1d-abb4-14c8aeca328c
-- title:
--   (2.1)–(2.2) — flip_{r,s} : Σ_{r+s} → walled diagrams is a bijection, so dim B_{r,s}(δ) = (r+s)!
-- statement:
--   For $r, s \ge 0$, let $\mathrm{flip}_{r,s}$ send a permutation $\sigma \in \Sigma_{r+s}$ to the walled Brauer diagram obtained from its permutation diagram (top vertex $a$ joined to bottom vertex $\sigma(a)$) by adding a wall between the $r$-th and $(r+1)$-th vertices and flipping the part of the diagram to the right of the wall in its horizontal axis. Then
--
--   1. $\mathrm{flip}_{r,s}$ is a bijection from $\Sigma_{r+s}$ onto the set of walled Brauer diagrams in $B_{r,s}(\delta)$, so it extends linearly to a vector space isomorphism $\mathrm{flip}_{r,s} : \mathbb C\Sigma_{r+s} \xrightarrow{\sim} B_{r,s}(\delta)$ (2.1);
--   2. consequently
--   $$
--   \dim B_{r,s}(\delta) = \dim \mathbb C\Sigma_{r+s} = (r+s)! \tag{2.2}
--   $$
--   that is, there are exactly $(r+s)!$ walled Brauer diagrams.
--
--   The bijection is the bookkeeping device that transports Schur–Weyl duality for $V^{\otimes(r+s)}$ to the mixed tensor space $V^{\otimes r} \otimes W^{\otimes s}$.
--
--   **Formalization Note** The isomorphism of (2.1) is stated on bases: `flipDiag r s` is bijective. The number of walled diagrams is `Nat.card (WalledDiagram r s)`.
-- source:
--   Brundan and Stroppel, Gradings on walled Brauer algebras and Khovanov's arc algebra, arXiv:1107.0999v1, p. 6, (2.1) and (2.2)

import Mathlib
import Definitions.Def_WalledBrauer_SuperSchurWeyl_Weights

namespace WalledBrauer.SuperSchurWeyl

open WalledBrauer.Blocks

/-- (2.1)–(2.2) (p. 6): `flip_{r,s}` is a bijection from `Σ_{r+s}` onto the walled Brauer
diagrams (so it extends to a vector space isomorphism `ℂΣ_{r+s} ≅ B_{r,s}(δ)`), and
`dim B_{r,s}(δ) = (r + s)!`. -/
theorem equation_2_1_2_2 (r s : ℕ) :
    Function.Bijective (flipDiag r s) ∧
    Nat.card (WalledDiagram r s) = (r + s).factorial := by sorry

end WalledBrauer.SuperSchurWeyl
