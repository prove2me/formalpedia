-- Prove2me | Theorems.Thm_SybilClinch_Supplement_theorem_4_13
-- name    : SybilClinch.Supplement.theorem_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:19:05.683645+00:00
-- url     : https://prove2.me/theorems/885d6fb3-e9aa-4b97-bf08-4c92fb1128ac
-- title:
--   Theorem 4.13 — weak Pareto optimality in the sell-$Y$ direction
-- statement:
--   Let an admissible AMM have initial spot price $p_0$, and let a finite profile consist of truthful eligible sell-$Y$ bids $(V_i,Q_i)$ with $V_i\ge p_0$. For every completed run of the one-sided AMM clinching mechanism, write $(x_i,y_i)$ for identity $i$'s terminal allocation of $X$ and payment of $Y$.
--
--   The resulting outcome is weakly Pareto optimal in both clauses of Definition 2.7:
--
--   1. no subset of eligible users can perform a feasible internal retrade of their post-batch holdings that weakly improves every user's utility and strictly improves at least one;
--   2. no eligible user can strictly improve its utility through an additional sell-$Y$-direction trade with the pool from the settled terminal reserve state.
--
--   Differences from the source:
--   - encoding: one-sided terminal allocation/payment $(x_i,y_i)$ → the published two-direction `Fill` with `sold = y_i`, `recv = x_i`, and a sell-$Y$ `Report`; reason: this is exactly the sell-$Y$ branch of Definition 2.7 and changes no outcome
--   - encoding: finite real one-sided values → `WithTop ℝ` values with an explicit non-top hypothesis and `untopD` only after that hypothesis; reason: the published one-sided run representation also serves the reverse auction, whose infinite values are excluded here as the paper requires
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), Theorem 4.13, printed p.20 (PDF p.22), in the setting of §3.1, printed p.8 (PDF p.10)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM_C
import Definitions.Def_SybilClinch_AdmissibleAMM_p0
import Definitions.Def_SybilClinch_chordMech
import Definitions.Def_SybilClinch_IsRun
import Definitions.Def_SybilClinch_OneSidedProfile_Valid
import Definitions.Def_SybilClinch_Run_pay
import Definitions.Def_SybilClinch_WeakPO

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

namespace Supplement

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and
Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256
93c5d05b05cc8b80b5bb5c0ac677b9642e119277d82de797234b0242f7c5021c), Theorem 4.13
(Weak Pareto optimality in the sell-`Y` direction), printed p.20 (PDF p.22).

For every admissible AMM, the truthful completed one-sided clinching outcome on finite eligible
sell-`Y` reports is weakly Pareto optimal in both senses of Definition 2.7: it admits neither a
strictly improving internal retrade among eligible users nor a strictly improving same-direction
trade between one such user and the pool.

**Formalization Note.** A one-sided terminal allocation `xᵢ` and payment `yᵢ` are embedded in the
published two-direction outcome format as `Fill(sold := yᵢ, recv := xᵢ)`. Finite `WithTop` values
are read with `untopD`; the finiteness hypothesis ensures the default is never used on the profile. -/
theorem theorem_4_13 (A : AdmissibleAMM) (P : OneSidedProfile) (hP : P.Valid)
    (hfin : ∀ i ∈ P.ids, P.v i ≠ ⊤)
    (helig : ∀ i ∈ P.ids, (A.p0 : WithTop ℝ) ≤ P.v i) (R : Run)
    (hR : IsRun (chordMech A.C A.p0 A.x0) P R) :
    let rep : ℕ → Report := fun i =>
      { dir := Dir.sellY, val := (P.v i).untopD 0, bud := P.q i }
    let f : ℕ → Fill := fun i =>
      { sold := R.pay (chordMech A.C A.p0 A.x0) i R.pf, recv := R.x i R.pf }
    WeakPO A P.ids rep f := by sorry

end Supplement

end SybilClinch
