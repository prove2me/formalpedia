-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_lemma_B_1
-- name    : PinwheelDensity.ExactRange.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:54.047079+00:00
-- url     : https://prove2.me/theorems/5fb05c18-9f74-40e8-970b-fc7877f65ece
-- title:
--   Lemma B.1 — a target lies in the root box of its cell
-- statement:
--   Let $m\ge1$ be an integer, $B\in\mathbb Q$ with $0\le B\le1$, let $A$ be a target (all entries at least $m$, $D(A)\le B$), and let $\theta=2h\ge4$ be even, with fold $b$, cell $c$ and root box $(\ell,u)$. Then:
--
--   1. $\ell_i\le b_i\le u_i$ and $b_i>0$ for all $i$, and $D(b)<\beta_\theta$;
--   2. $\mathrm{wt}_\theta(c)<\beta_\theta$;
--   3. the entries of $c$ below $h$ are, as a multiset, exactly the entries of $A$ below $h$;
--   4. if $b$ is schedulable, then so is $A$.
--
--   It is what lets a certificate for the cell apply to every target with that cell.
--
--   Differences from the source:
--   - encoding: $R_\theta(x)=x$ for $x\le h$ → natural-valued, with $\lfloor x\rfloor$ on the low branch; reason: the source records the same choice for its Lean (p. 11); the two agree on the integers that occur there
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Lemma B.1, p. 12 (PDF p. 12)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_cellOf

namespace PinwheelDensity.ExactRange

/-- Lemma B.1 (Cells), p. 12, under the standing assumptions of Appendix B, p. 11:
`1 ≤ m`, `0 ≤ B ≤ 1`, `θ = 2h ≥ 4` even. -/
theorem lemma_B_1 (m : ℕ) (hm : 1 ≤ m) (B : ℚ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (θ : ℕ) (hθ : Even θ) (hθ4 : 4 ≤ θ) (A : List ℕ) (hA : IsTarget m B A) :
    IsBoxMember (rootLo (cellOf θ A)) (rootUp θ (cellOf θ A)) (beta B θ) (foldOf θ A) ∧
    weight θ (cellOf θ A) < beta B θ ∧
    ((cellOf θ A).filter (fun x => x < θ / 2)).Perm (A.filter (fun x => x < θ / 2)) ∧
    (RatSchedulable (foldOf θ A) → RatSchedulable (toQ A)) := by sorry

end PinwheelDensity.ExactRange
