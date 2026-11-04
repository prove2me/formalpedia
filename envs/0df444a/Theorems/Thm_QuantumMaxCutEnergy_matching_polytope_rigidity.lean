-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_matching_polytope_rigidity
-- name    : QuantumMaxCutEnergy.matching_polytope_rigidity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-03T06:54:57.813497+00:00
-- url     : https://prove2.me/theorems/bcaa13c6-28e8-4709-afdf-ba158eae3fb8
-- title:
--   Rigidity: a constraint-isolated point of the odd-set polytope is integral
-- statement:
--   **Rigidity of the odd-set polytope: a constraint-isolated point is integral.**
--
--   Let $x\ge0$ with all vertex loads at most $1$ and all odd-set masses at most $(|S|-1)/2$. Suppose $x$ is
--   *constraint-isolated*: the only edge direction $d$ that vanishes outside the support of $x$, leaves every
--   *saturated* vertex load unchanged (i.e. $\sum_{e\ni v}d_e=0$ whenever $\mathrm{load}_x(v)=1$) and leaves every
--   *tight* odd-set mass unchanged is $d=0$. Then every value of $x$ is $0$ or $1$.
--
--   Equivalently: every vertex of the fractional matching polytope of Edmonds is the incidence vector of a matching.
--
--   **Route.** Take the family $L$ of tight odd sets and laminarize it by the odd-case uncrossing
--   (`QuantumMaxCutEnergy.tight_odd_uncross`); by `QuantumMaxCutEnergy.laminar_internal_independent` the tight odd
--   rows of a laminar family are linearly independent on the support, and together with the tight vertex-load rows
--   they determine the coordinates of any direction supported on the support; isolation then forces every
--   coordinate of $x$ on the support to sit at a boundary of its range, i.e. to be $0$ or $1$. If some coordinate
--   were strictly between $0$ and $1$, a nonzero direction could be constructed along the laminar structure — this
--   last construction is the part of the argument that is not yet formalized, which is why this node is Open.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Schrijver, Combinatorial Optimization, Ch. 25, Sec. 25.2 (vertices of the matching polytope are integral).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Rigidity of the odd-set polytope.** A point of the odd-set polytope that is *constraint-isolated* —
the only direction supported on its support that is orthogonal to every tight constraint is zero — is
integral. This is the statement that every vertex of the fractional matching polytope is a matching. -/
theorem matching_polytope_rigidity {n : ℕ} (x : Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, loadAt x v ≤ 1)
    (hodd : ∀ S : Finset (Fin n), Odd S.card → internalSum x S ≤ ((S.card : ℝ) - 1) / 2)
    (hiso : ∀ d : Edge n → ℝ,
      (∀ e, x e = 0 → d e = 0) →
      (∀ v : Fin n, loadAt x v = 1 →
        (∑ e, if v = e.val.1 ∨ v = e.val.2 then d e else 0) = 0) →
      (∀ S : Finset (Fin n), Odd S.card → internalSum x S = ((S.card : ℝ) - 1) / 2 →
        (∑ e ∈ Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S), d e) = 0) →
      d = 0) :
    ∀ e, x e = 0 ∨ x e = 1 := by sorry

end QuantumMaxCutEnergy
