-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_prop_B_5
-- name    : PinwheelDensity.ExactRange.prop_B_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:06.407777+00:00
-- url     : https://prove2.me/theorems/1d087ccf-030c-4e2f-b56d-3d5d75ee42f4
-- title:
--   Proposition B.5 — adjacent-stage unfolding gives the complete next case set
-- statement:
--   Let $m\ge1$, $0\le B\le1$, let $\theta=2h\ge4$ be even, $A$ a target, $c$ its cell at stage $\theta$ and $c'$ its cell at stage $\theta+2$. Let $n_h$ be the number of entries of $c$ equal to $h$, $n_{\theta-1}$ the number equal to $\theta-1$, and $c_0$ the remaining entries. Then there are integers $g,p\ge0$ with $g+p\le n_h$, $o\in\{0,1\}$ with $o\le n_{\theta-1}$, and $0\le v\le2g+o$ such that, as multisets,
--   $$c'=c_0+[h]^{n_h-g-p}+[h+1]^p+[\theta-1]^{n_{\theta-1}-o}+[\theta]^{2g+o-v}+[\theta+1]^v,$$
--   and $\mathrm{wt}_{\theta+2}(c')<\beta_{\theta+2}$. The generator $U_\theta^B(c)$ is the list of all sorted lists of this form over the admissible $(g,p,o,v)$ that pass this weight filter; in particular it contains $c'$.
--
--   It guarantees that passing from a residual cell to the next stage loses no target.
--
--   Differences from the source:
--   - encoding: $R_\theta(x)=x$ for $x\le h$ → natural-valued, with $\lfloor x\rfloor$ on the low branch; reason: the source records the same choice for its Lean (p. 11); the two agree on the integers that occur there
--   - encoding: $U_\theta^B(c)$ is the list of all sorted lists of this form → a membership characterization of `unfoldCell`, for every list $c$, together with $c'\in U_\theta^B(c)$; reason: the order and multiplicity of the output carry no content; the membership of $c'$ is what the sentence is used for
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Proposition B.5, p. 13 (PDF p. 13)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_cellOf

namespace PinwheelDensity.ExactRange

/-- Proposition B.5 (Adjacent-stage unfolding), p. 13: the cell at stage `θ + 2` has the displayed
form for some admissible `(g, p, o, v)`, satisfies the strict weight filter, and is output by the
generator; and the generator consists exactly of the sorted lists of this form passing the filter. -/
theorem prop_B_5 (B : ℚ) (θ : ℕ) (hθ : Even θ) (hθ4 : 4 ≤ θ) :
    (∀ (m : ℕ) (A : List ℕ), 1 ≤ m → 0 ≤ B → B ≤ 1 → IsTarget m B A →
      (∃ g p o v : ℕ, UnfoldAdmissible θ (cellOf θ A) g p o v ∧
        (cellOf (θ + 2) A).Perm (unfoldForm θ (cellOf θ A) g p o v)) ∧
      weight (θ + 2) (cellOf (θ + 2) A) < beta B (θ + 2) ∧
      cellOf (θ + 2) A ∈ unfoldCell B θ (cellOf θ A)) ∧
    (∀ c d : List ℕ, d ∈ unfoldCell B θ c ↔
      ∃ g p o v : ℕ, UnfoldAdmissible θ c g p o v ∧
        d = (unfoldForm θ c g p o v).insertionSort (· ≤ ·) ∧
        weight (θ + 2) d < beta B (θ + 2)) := by sorry

end PinwheelDensity.ExactRange
