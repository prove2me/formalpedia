-- Prove2me | Theorems.Thm_TwoBoxMemory_Supplement_theorem_C_6
-- name    : TwoBoxMemory.Supplement.theorem_C_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:15:28.002102+00:00
-- url     : https://prove2.me/theorems/edc900b7-4839-436e-87c7-69154923f432
-- title:
--   Theorem C.6 — same-budget completeness and semidecidability of a strict excess target
-- statement:
--   Let $r,s\in(0,1)$ and $C,D>0$ be rational, $M\ge1$ an integer and $\varepsilon>0$ rational, and let $V$ be the unrestricted value (the infimum of $\max(J_A,J_B)$ over all probability laws on command words). The following are equivalent:
--
--   1. some real controller with at most $M$ labels has worst risk strictly less than $V+\varepsilon$;
--   2. some rational controller with at most $M$ labels has worst risk strictly less than $V+\varepsilon$;
--   3. some rational certificate — a rational candidate controller with at most $M$ labels, nonnegative rational Bellman supersolutions $v_A\ge c+Q_Av_A$, $v_B\ge c+Q_Bv_B$, a horizon $T$, a rational prior $\pi\in[0,1]$ and a rational array $Y$ satisfying (A.20) — has
--
--   $$U-L<\varepsilon,\qquad L=\max(0,Y_{0,0}-E_T),\quad U=\max(\mu v_A,\mu v_B),$$
--
--   with $E_T$ the completion allowance (A.8).
--
--   Moreover these equivalent conditions are semidecidable: the set of inputs $(r,s,C,D,M,\varepsilon)$ (rationals given by integer codes) that are in the above range and satisfy them is recursively enumerable.
--
--   The theorem says that strict near-optimality within a label budget always has a finite rational witness that can be found by search.
--
--   Differences from the source:
--   - reading: enumeration of rational controllers and rational certificates semidecides these equivalent conditions → each of the three conditions, conjoined with the input range, is a recursively enumerable predicate (`REPred`) on coded inputs; reason: semidecidability is r.e.-ness of the set of accepted inputs; the enumeration is the proof method
--   - encoding: rational inputs → each rational coded as an integer pair (n, d) denoting n/(d + 1); reason: an explicit computable encoding of ℚ; every rational has a code
--   - encoding: worst risk strictly less than V + ε → `worstRisk < value + ENNReal.ofReal ε` in `ℝ≥0∞`; reason: Lean convention; same instances
--   - encoding: commands A, B; risks in [0, ∞] → commands `Fin 2` with 0 = A, 1 = B; risks in `ℝ≥0∞`; reason: Lean convention; same instances
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Theorem C.6, p.31 (PDF 33); certificate of §C.3, p.31 (PDF 33), with (A.20)–(A.21), pp.18–19 (PDF 20–21) and (A.8), p.15 (PDF 17)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Supplement_Rational
import Definitions.Def_TwoBoxMemory_Supplement_Certificate

namespace TwoBoxMemory.Supplement

open TwoBoxMemory

/-- Theorem C.6 (Same-budget completeness for a strict excess target). For rational physical
inputs (`0 < r, s < 1`, `C, D > 0` rational), integer `M ≥ 1` and rational `ε > 0`, the following
are equivalent:
1. some real controller with at most `M` labels has worst risk strictly less than `V + ε`;
2. some rational controller with at most `M` labels has this property;
3. a rational certificate (§C.3: rational candidate controller, nonnegative rational supersolutions
   (A.21), horizon `T`, rational prior `π ∈ [0, 1]`, rational array satisfying (A.20)) has at most
   `M` controller labels and `U − L < ε`, where `L = max(0, Y_{0,0} − E_T)`,
   `U = max(µ v_A, µ v_B)`.
Moreover these equivalent conditions are semidecidable: the set of (codes of) valid inputs
`(r, s, C, D, M, ε)` satisfying them is recursively enumerable.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Theorem C.6, p.31 (PDF 33); certificate of §C.3, p.31, with (A.20)–(A.21), pp.18–19 (PDF 20–21),
`E_T` of (A.8), p.15 (PDF 17).

**Formalization Note.** `V` is the published `value` (infimum over all laws on words), `W` the
published `worstRisk` in `ℝ≥0∞`; "`< V + ε`" is `worstRisk < value + ENNReal.ofReal ε`.
Semidecidability ("enumeration … semidecides") is Mathlib's `REPred` on the input codes
`C6Input` (each rational coded as `(n, d) ↦ n/(d+1)`, `RatCode`), applied to "the input is valid
and the condition holds"; it is stated for each of the three conditions. The paper's sentence that
no termination claim is made at the boundary is a disclaimer and is not stated. -/
theorem theorem_C_6 :
    (∀ (r s C D ε : ℚ) (M : ℕ), 0 < r → r < 1 → 0 < s → s < 1 → 0 < C → 0 < D → 1 ≤ M →
      0 < ε →
        (C6Cond1 r s C D M ε ↔ C6Cond2 r s C D M ε) ∧
        (C6Cond2 r s C D M ε ↔ C6Cond3 r s C D M ε)) ∧
    REPred (fun x : C6Input => C6Valid x ∧
      C6Cond1 x.1.val x.2.1.val x.2.2.1.val x.2.2.2.1.val x.2.2.2.2.1 x.2.2.2.2.2.val) ∧
    REPred (fun x : C6Input => C6Valid x ∧
      C6Cond2 x.1.val x.2.1.val x.2.2.1.val x.2.2.2.1.val x.2.2.2.2.1 x.2.2.2.2.2.val) ∧
    REPred (fun x : C6Input => C6Valid x ∧
      C6Cond3 x.1.val x.2.1.val x.2.2.1.val x.2.2.2.1.val x.2.2.2.2.1 x.2.2.2.2.2.val) := by sorry

end TwoBoxMemory.Supplement
