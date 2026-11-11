-- Prove2me | Theorems.Thm_WaitFreeTasks_Characterization_decision_map_carried
-- name    : WaitFreeTasks.Characterization.decision_map_carried
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:16.690293+00:00
-- url     : https://prove2.me/theorems/85eece35-35ff-4026-b97a-56473e5576c4
-- title:
--   Lemma 14 — Decision map is carried by the task specification
-- statement:
--   Let $T=(I,O,\Delta)$ be a chromatic task for $n\ge2$ processes, with the finite complexes and chromatic, monotone, pure carrier of Section 2. Fix a carried PL finite-to-one map $f:|I|\to|O|$ and a geometric subdivision $D=\operatorname{div}(I)$ on whose simplices $f$ is affine and whose simplex images lie in output simplices, as in Section 4.1.
--
--   List all output simplices as $\Sigma_1,\ldots,\Sigma_m$ in nondecreasing dimension. A run means the actual push-down and descending shatter loops of Section 4.2, starting with $D$ and the minimum image-carrier coloring $\operatorname{col}$ of Definition 2. Write $K_t$ and $\operatorname{col}_t$ for its state after phase $t$, and $D'=K_m$, $\operatorname{col}'=\operatorname{col}_m$ for its output. No correctness invariant is assumed in the definition of a run.
--
--   Let $\phi$ be the map specified by Definition 5 on the actual vertices of $D'$. It is carried by the original task carrier:
--
--   $$\phi(\sigma')\in\Delta(\operatorname{carr}_I(\sigma'))\quad(\sigma'\in D').$$
--
--   The carrier on the right is the minimal original input face containing the whole fine simplex. The output image on the left is the set of its image vertices. This is a property of the constructed decision map, not a condition imposed on an arbitrary chromatic map.
--
--   Differences from the source:
--   - encoding: maps between finite complex realizations → ambient real coordinate functions restricted to the realizations, with faces stored as finite sets; reason: every real barycentric point is included; values off the realizations are irrelevant and extend arbitrarily
--   - encoding: identifiers in [n] = {1,...,n} → identifiers in Fin n = {0,...,n-1}; reason: subtracting one is an order preserving bijection; all n >= 2 remain quantified
--   - encoding: states after the procedure handles each output simplex → a finite run relation with phase boundaries indexed by naturals; reason: only atomic stellar operations and loop exit tests are assumed; no successful-refinement invariant is an input
--   - encoding: the unique image-carrier vertex of the assigned color → a relation on maps from the actual vertex subtype; reason: Lemma 13 establishes existence and pointwise uniqueness; empty domains require no output default
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), p. 17 (PDF p. 19), Lemma 14

import Definitions.Def_WaitFreeTasks_Characterization_Refinement

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-- **Lemma 14** (Attiya–Paz, STOC 2027 submission #828 (October 2026), printed p. 17, PDF p. 19). Setting of §4: `T` is a chromatic task for `n ≥ 2` processes, `f : |I| → |O|` is PL,
finite-to-one and carried by `Δ`, and `D = div(I)` is a subdivision of `I` with the property of
Lemma 2 (`f` linear on each simplex of `D`, mapping it into a simplex of `O`).
Let `Σ_1, …, Σ_m` (`ord`) be the simplices of `O` in the non-decreasing order of dimension
in which they are handled, and let `st` be a completed run of the refinement procedure of §4.2
from `(div(I), col)`, so that `K_t = (st t).1` (with colouring `(st t).2`) is the subdivision
after handling `Σ_t`. The map `φ : div'(I) → O` of Definition 5 is carried by `Δ`: for every simplex `σ'` of
`div'(I)`, `φ(σ') ∈ Δ(carr_I(σ'))`. -/
theorem decision_map_carried {n : ℕ} {VI VO : Type} (hn : 2 ≤ n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) (hPL : IsPL T.I.real f) (hfin : FiniteToOne T.I.real T.O.real f)
    (hcar : IsCarried T f) (D : GCx (VI → ℝ)) (hD : IsSubdivOf D T.I) (hDf : IsAdapted T f D)
    (ord : List (Finset VO)) (hord : IsHandlingOrder T ord) (st : ℕ → RState n VI)
    (hrun : IsRun (by omega) T f D ord st) :
    ∀ φ : VertexMap (st ord.length).1 VO, IsDecisionMap T f (st ord.length).1 (st ord.length).2 φ →
      ∀ σ' ∈ (st ord.length).1, vertexImage (st ord.length).1 σ' φ ∈ T.Δ (carrOf T.I.faces (gs σ')) := by sorry

end WaitFreeTasks.Characterization
