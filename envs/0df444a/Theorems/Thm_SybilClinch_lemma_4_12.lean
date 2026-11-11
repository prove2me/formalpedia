-- Prove2me | Theorems.Thm_SybilClinch_lemma_4_12
-- name    : SybilClinch.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:45:32.281394+00:00
-- url     : https://prove2.me/theorems/523f8cca-c495-4273-8992-fa9cc148a7ee
-- title:
--   Lemma 4.12 — terminal certificate of a truthful one-sided run
-- statement:
--   Let $K$ be an admissible cost on $[0,\mathrm{cap})$ with initial right derivative $p_\star$, and consider any completed truthful run of the one-sided clinching auction it generates (finite nonnegative reports read as true types). Let $r_i:=Q_i-y_i$ be the terminal unspent budget of identity $i$ and $a(X_f)=K'_+(X_f)$ the terminal right marginal ask. Then:
--
--   1. if $x_j>0$ and $V_i>V_j$, then $r_i=0$;
--   2. if $r_i>0$, then $V_i\le a(X_f)$.
--
--   Differences from the source:
--   - generalization: the one-sided AMM clinching auction on the pool cost C (initial price p0, capacity x0) → the auction chordMech K pstar cap of any cost K with IsAdmissibleCost K pstar cap; reason: Lemma 6.1 states that the proof uses only these cost properties and applies the result to C̃_M and C̃^rev_M; C on [0, x0) with pstar = p0 is an admissible cost, so the Lean statement specializes to the source's
--   - reading: continuous evolution by the primitive conditions (16)–(18) on event-free open intervals, on which the clock and state paths are absolutely continuous → IsRun: the event procedure is applied at every clock price; off Clinch the continuous part of dx_i has no mass; a clincher stays at the water level on a right neighbourhood of every price while active; no absolute-continuity requirement on the paths; reason: event prices may accumulate (lumps of an admissible target can be dense) and, for an admissible AMM whose right marginal ask is flat on a fat Cantor set, the sole-survivor path X = Z(p) is continuous but not absolutely continuous, so a literal AC requirement would admit no run; on event-free intervals with AC paths the two formulations coincide
--   - reading: reported values (v_i, q_i) ∈ ℝ²≥0 in the one-sided analysis → values in WithTop ℝ with the hypothesis v_i ≠ ⊤ for every identity; reason: the paper states that its one-sided analysis allows only finite-value reports (p.28); infinite values are the subject of Lemma 6.2
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.5, Lemma 4.12, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_SybilClinch_IsRun
import Definitions.Def_SybilClinch_IsAdmissibleCost
import Definitions.Def_SybilClinch_chordMech
import Definitions.Def_SybilClinch_OneSidedProfile_Valid
import Definitions.Def_SybilClinch_Run_alloc

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.5, Lemma 4.12 (Terminal certificate), printed p.20 (PDF p.22).

Every completed truthful one-sided run satisfies, with `rᵢ := Qᵢ − yᵢ` the terminal unspent budget
and `a(X_f) = K′₊(X_f)` the terminal right marginal ask:
1. if `xⱼ > 0` and `Vᵢ > Vⱼ`, then `rᵢ = 0`;
2. if `rᵢ > 0`, then `Vᵢ ≤ a(X_f)`.

**Formalization Note.** Generalized to any admissible cost `K` (Lemma 6.1); the paper's case is
`K = C`. The right derivative is `derivWithin K (Ici X_f) X_f`, which exists since `K` is convex and
`X_f < cap`. Values are finite. -/
theorem lemma_4_12 (K : ℝ → ℝ) (pstar cap : ℝ) (hK : IsAdmissibleCost K pstar cap)
    (P : OneSidedProfile) (hP : P.Valid) (hfin : ∀ i ∈ P.ids, P.v i ≠ ⊤) (R : Run)
    (hR : IsRun (chordMech K pstar cap) P R) :
    (∀ i ∈ P.ids, ∀ j ∈ P.ids, 0 < R.x j R.pf → P.v j < P.v i →
      P.q i - R.pay (chordMech K pstar cap) i R.pf = 0) ∧
    ∀ i ∈ P.ids, 0 < P.q i - R.pay (chordMech K pstar cap) i R.pf →
      P.v i ≤ ((derivWithin K (Ici (R.alloc P.ids R.pf)) (R.alloc P.ids R.pf) : ℝ) :
        WithTop ℝ) := by sorry

end SybilClinch
