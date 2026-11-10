-- Prove2me | Theorems.Thm_RobersonCx_theorem_11
-- name    : RobersonCx.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:39.813723+00:00
-- url     : https://prove2.me/theorems/3b2746e6-0fd6-40e8-b4ae-ac7a58cd716f
-- title:
--   Theorem 11 — $D^{(r)}_q$, $B^{(r)}_q$ lie in the closures of their own Forb classes, which are not h.d.-closed
-- statement:
--   Let $r\ge2$ admit an invertible residue class modulo $r$ other than $\pm1$, and let $q\equiv1\pmod r$ with $q>4r^2-2r$. Then
--   $$D^{(r)}_q\in\mathrm{Cl}\big(\mathrm{Forb}_{\mathrm m}(D^{(r)}_q)\big),\qquad B^{(r)}_q\in\mathrm{Cl}\big(\mathrm{Forb}_{\mathrm m}(B^{(r)}_q)\big),\qquad B^{(r)}_q\in\mathrm{Cl}\big(\mathrm{Forb}_{\mathrm{imm}}(B^{(r)}_q)\big).$$
--   Moreover:
--
--   1. $\mathrm{Forb}_{\mathrm m}(D^{(r)}_q)$ is closed under minors and disjoint unions but is not h.d.-closed;
--   2. $\mathrm{Forb}_{\mathrm m}(B^{(r)}_q)$ is closed under minors and disjoint unions but is not h.d.-closed;
--   3. $\mathrm{Forb}_{\mathrm{imm}}(B^{(r)}_q)$ is closed under immersions and disjoint unions but is not h.d.-closed.
--
--   These are infinite families of counterexamples to the Strong Roberson Conjecture and to its immersion analogue; $r=5$, $q=91$ gives the fixed graphs of Theorem 2.
--
--   Differences from the source:
--   - encoding: invertible residue class modulo $r$ other than $\pm1$; $q\equiv1\pmod r$ → a unit $a$ of `ZMod r` with $a\ne1$, $a\ne-1$; $(q:\mathbb Z_r)=1$; reason: same instances
--   - encoding: $q>4r^2-2r$ → $4r^2<q+2r$ in $\mathbb N$; reason: avoids natural-number subtraction; same instances
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Theorem 11, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_RobersonCx_InCl
import Definitions.Def_RobersonCx_ForbMinor
import Definitions.Def_RobersonCx_circulantD

set_option autoImplicit false

namespace RobersonCx

/-- Theorem 11 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §4.2, p.10 (PDF p.12)). Let `r ≥ 2` admit an invertible residue class other than `±1`, and
let `q ≡ 1 (mod r)` with `q > 4r² − 2r`. Then `D^(r)_q ∈ Cl(Forb_m(D^(r)_q))`, `B^(r)_q ∈ Cl(Forb_m(B^(r)_q))`,
`B^(r)_q ∈ Cl(Forb_imm(B^(r)_q))`. Thus `Forb_m(D^(r)_q)` and `Forb_m(B^(r)_q)` are closed under minors and disjoint
unions, but are not h.d.-closed. Likewise, `Forb_imm(B^(r)_q)` is closed under immersions and disjoint unions, but
is not h.d.-closed.

**Formalization Note** "Invertible residue class other than `±1`" is a unit `a` of `ZMod r` with `a ≠ 1`,
`a ≠ −1`; `q ≡ 1 (mod r)` is `(q : ZMod r) = 1`; `q > 4r² − 2r` is `4r² < q + 2r`. All three memberships and the
nine closure clauses of the "Thus" sentence are stated. -/
theorem theorem_11 (r q : ℕ) (hr : 2 ≤ r) (hunit : ∃ a : ZMod r, IsUnit a ∧ a ≠ 1 ∧ a ≠ -1)
    (hq1 : (q : ZMod r) = 1) (hq : 4 * r ^ 2 < q + 2 * r) :
    InCl (ForbMinor (circulantD q r)) (circulantD q r) ∧
    InCl (ForbMinor (splitB q r)) (splitB q r) ∧
    InCl (ForbImm (splitB q r)) (splitB q r) ∧
    (MinorClosed (ForbMinor (circulantD q r)) ∧ DisjUnionClosed (ForbMinor (circulantD q r)) ∧
      ¬ IsHDClosed (ForbMinor (circulantD q r))) ∧
    (MinorClosed (ForbMinor (splitB q r)) ∧ DisjUnionClosed (ForbMinor (splitB q r)) ∧
      ¬ IsHDClosed (ForbMinor (splitB q r))) ∧
    (ImmersionClosed (ForbImm (splitB q r)) ∧ DisjUnionClosed (ForbImm (splitB q r)) ∧
      ¬ IsHDClosed (ForbImm (splitB q r))) := by sorry

end RobersonCx
