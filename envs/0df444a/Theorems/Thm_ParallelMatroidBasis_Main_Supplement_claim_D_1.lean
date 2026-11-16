-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_Supplement_claim_D_1
-- name    : ParallelMatroidBasis.Main.Supplement.claim_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:01:33.964189+00:00
-- url     : https://prove2.me/theorems/d308d4b8-25d4-44f6-87ba-44d7cb67261e
-- title:
--   Claim D.1 ([Nel16]) — at most $2^{n^3/4}$ linear matroids on an $n$-element ground set, $n\ge 12$
-- statement:
--   For an integer $n\ge 12$, let $\mathcal L_n$ be the set of linear matroids with ground set $[n]$: matroids $M$ on $[n]$ for which there are a field $\mathbb F$ and vectors $v_1,\dots,v_n$ in some $\mathbb F^k$ with $S\in\mathcal I\iff(v_i)_{i\in S}$ linearly independent. Then $\mathcal L_n$ is finite and
--   $$|\mathcal L_n|\ \le\ 2^{n^3/4}.$$
--
--   The statement counts labelled matroids on the fixed ground set $[n]$, not isomorphism classes. The source attributes it to Nelson [Nel16]. It is the union bound that lets the proof of Theorem 1.3 fix one choice of random bits that works for every linear matroid at once.
--
--   **Formalization Note** $\mathcal L_n$ is the set of `Matroid (Fin n)` with ground set `univ` satisfying `IsLinearMatroid`; its finiteness is stated so that the cardinality bound is not satisfied by the convention that an infinite set has `ncard` $0$. The exponent $n^3/4$ is a real number.
--
--   Differences from the source:
--   - generalization: linear matroid: representable by vectors over a field F_q → representable (RandDelMatroid.Indep.IsRepresentableOver) over some field F : Type, finite or not, vectors in F^k for some k, repeated vectors allowed; reason: every F_q-representable matroid is included, so the Lean statement specializes to the source's; the cited bound [Nel16] counts matroids representable over any field, and the proof of Theorem 1.3 uses only that count
--   - encoding: linear matroids on a fixed n-element ground set → Matroid (Fin n) with ground set univ, counted as a set of matroids (labelled), with finiteness of the set stated; reason: the count is over matroids on the fixed ground set, not isomorphism classes; stating finiteness only rules out the ncard-of-an-infinite-set junk value
--   - encoding: 2^{n^3/4} → (2 : ℝ) ^ ((n : ℝ)^3 / 4), compared with the cardinality cast to ℝ; reason: n³/4 need not be an integer
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Claim D.1 ([Nel16]), p.39 (PDF p.41); used in the proof of Theorem 1.3, p.39 (PDF p.41); linear matroids: §1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_Supplement_Classes

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main.Supplement

/-- Claim D.1 ([Nel16]), PDF p.41 (printed p.39). For `n ≥ 12` the set of linear matroids with
ground set `Fin n` (representable over some field) is finite and has at most `2^{n³/4}` elements. -/
theorem claim_D_1 (n : ℕ) (hn : 12 ≤ n) :
    {M : Matroid (Fin n) | M.E = Set.univ ∧ IsLinearMatroid M}.Finite ∧
      (({M : Matroid (Fin n) | M.E = Set.univ ∧ IsLinearMatroid M}.ncard : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((n : ℝ) ^ 3 / 4) := by sorry

end ParallelMatroidBasis.Main.Supplement
