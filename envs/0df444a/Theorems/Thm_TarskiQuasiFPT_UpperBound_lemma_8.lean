-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_lemma_8
-- name    : TarskiQuasiFPT.UpperBound.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:44.510598+00:00
-- url     : https://prove2.me/theorems/423d1312-03b0-489d-9d20-320b4d471839
-- title:
--   Lemma 8 — an empty $\mathrm{Fix}^-$ ($\mathrm{Fix}^+$) makes $J(Q)$ ($M(Q)$) a positive (negative) solution
-- statement:
--   Let $Q$ be a safe query-answer set (the standing assumption of §2.4).
--
--   1. If $\mathrm{Fix}^-(Q)=\emptyset$, then $J(Q)$ is a positive solution of every safe $g\Rightarrow Q$.
--   2. If $\mathrm{Fix}^+(Q)=\emptyset$, then $M(Q)$ is a negative solution of every safe $g\Rightarrow Q$.
--
--   Once one of the two candidate sets is empty, a solution is known without further queries.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: n ≥ 1 (standing: [n] is nonempty) → type-class hypothesis [NeZero n]; reason: the same condition, needed so that J_s(Q), M_s(Q) (a finite join/meet of grid points) are defined
--   - encoding: query-answer set: a finite set of pairs (x, r) with distinct x; Q ⊆ Q′ as sets of pairs → QASet n k = Point n k → Option (Point n k × Label) (Q x = some r iff (x, r) ∈ Q); QASubset Q Q′ is inclusion of recorded pairs; reason: a partial function on the finite grid is exactly a finite set of pairs with distinct first components
--   - encoding: labels in {±1} with −1 < +1; positive solution (x,0) ⪯ f(x), negative solution f(x) ⪯ (x,0) → Label = {neg < pos}; IsPosSolution f x := x ⪯ (f x).1 ∧ (f x).2 = pos, IsNegSolution f x := (f x).1 ⪯ x ∧ (f x).2 = neg; reason: 0 lies strictly between −1 and +1, so 0 ≤ label iff label = +1 and label ≤ 0 iff label = −1
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Lemma 8, PDF p. 9 (printed p. 8); standing assumption 'Let Q be a safe query-answer set', §2.4, PDF p. 7

import Mathlib
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryAnswerSets

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-- Lemma 8 (PDF p. 9), for a safe query-answer set `Q` (standing assumption of §2.4): if
`Fix⁻(Q) = ∅` then `J(Q)` is a positive solution of every safe `g ⇒ Q`; if `Fix⁺(Q) = ∅` then
`M(Q)` is a negative solution of every safe `g ⇒ Q`. -/
theorem lemma_8 {n k : ℕ} [NeZero n] (Q : QASet n k) (hQ : IsSafeQA Q) :
    (FixMinus Q = ∅ → ∀ g : Point n k → Point n k × Label, IsSafe g → Consistent g Q →
        IsPosSolution g (J Q)) ∧
    (FixPlus Q = ∅ → ∀ g : Point n k → Point n k × Label, IsSafe g → Consistent g Q →
        IsNegSolution g (M Q)) := by sorry

end TarskiQuasiFPT.UpperBound
