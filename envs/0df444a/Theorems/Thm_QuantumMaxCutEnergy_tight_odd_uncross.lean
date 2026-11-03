-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_tight_odd_uncross
-- name    : QuantumMaxCutEnergy.tight_odd_uncross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T05:07:33.15509+00:00
-- url     : https://prove2.me/theorems/518eb152-2d01-4c15-8fe5-49c7f3abc332
-- title:
--   Odd-set uncrossing: crossing tight odd sets give a tight intersection and union
-- statement:
--   **Odd-set uncrossing.**
--
--   Let $x\ge0$ satisfy the odd-set constraints $\mathrm{internalSum}\,x\,S\le(|S|-1)/2$ for every odd $S$, and
--   suppose the odd sets $A$, $B$ are both *tight* for $x$, with $|A\cap B|$ odd. Then the intersection and the
--   union are odd and tight as well:
--   $$\mathrm{internalSum}\,x\,(A\cap B)=\frac{|A\cap B|-1}{2},\qquad
--   \mathrm{internalSum}\,x\,(A\cup B)=\frac{|A\cup B|-1}{2}.$$
--
--   **Proof.** The uncrossing identity gives
--   $\mathrm{internalSum}\,x\,(A\cup B)+\mathrm{internalSum}\,x\,(A\cap B)\ge\mathrm{internalSum}\,x\,A+\mathrm{internalSum}\,x\,B
--   =\frac{|A|-1}{2}+\frac{|B|-1}{2}$, while the odd-set constraints for $A\cup B$ and $A\cap B$ (both odd, since
--   $|A|+|B|=|A\cup B|+|A\cap B|$) give the reverse inequality with the same total
--   $\frac{|A\cup B|-1}{2}+\frac{|A\cap B|-1}{2}=\frac{|A|-1}{2}+\frac{|B|-1}{2}$. Hence equality holds in both.
--
--   **Role.** This is the uncrossing step of the route to Edmonds' exactness of the matching polytope: iterating it
--   replaces any family of tight odd sets by a laminar one, which is the hypothesis under which the rigidity (hence
--   integrality) of a polytope vertex can be shown. It is the point where the odd-set constraints — and not only the
--   vertex loads — are used, i.e. exactly the odd-cycle information missing from the bipartite case
--   (`QuantumMaxCutEnergy.matching_dominated_of_bipartite`).
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Schrijver, Combinatorial Optimization, Ch. 25, Section 25.2 (laminarization of the tight odd sets).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Odd-set uncrossing**: two crossing tight odd sets can be replaced by their intersection and union, which
are again tight. -/
theorem tight_odd_uncross {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hcon : ∀ S : Finset (Fin n), Odd S.card → internalSum x S ≤ ((S.card : ℝ) - 1) / 2)
    (A B : Finset (Fin n)) (hAodd : Odd A.card) (hBodd : Odd B.card)
    (hAiB : Odd (A ∩ B).card)
    (hA : internalSum x A = ((A.card : ℝ) - 1) / 2)
    (hB : internalSum x B = ((B.card : ℝ) - 1) / 2) :
    internalSum x (A ∩ B) = (((A ∩ B).card : ℝ) - 1) / 2 ∧
      internalSum x (A ∪ B) = (((A ∪ B).card : ℝ) - 1) / 2 := by sorry

end QuantumMaxCutEnergy
