-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_informational_distance_properties
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.informational_distance_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:58:45.274241+00:00
-- url     : https://prove2.me/theorems/0bbd177c-b791-48f8-bbe6-4b8791f573b6
-- title:
--   All five properties of informational distance
-- statement:
--   Let $\rho_{ABC}$ be any normalized state on finite-dimensional complex systems. For each indicated marginal define $D(U:V)=\|\rho_{UV}-\rho_U\otimes\rho_V\|_1$, and use mutual information $S(U:V)$ in bits. All of the following hold:
--
--   1. $D(A:B)=D(B:A)$, with the two tensor factors exchanged.
--   2. $D(AB:C)\ge D(A:C)$, where $B$ is traced out on the right.
--   3. $0\le D(A:B)\le2$.
--   4. For every finite-dimensional CPTP map $F$ on $AB$, $D(A:B)\ge\|F(\rho_{AB})-F(\rho_A\otimes\rho_B)\|_1$.
--   5. The source's stated estimate is
--   $$
--   D(A:B)\le\sqrt{2S(A:B)}.
--   $$
--
--   These properties make informational distance compatible with exchanging subsystems, discarding subsystems and physical processing. Clause 5 keeps the printed weaker constant.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 11, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Lemma 2, PDF p.11: all five clauses, with explicit swap, regrouping and marginalization. -/
theorem informational_distance_properties {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (rho : Matrix ((A × B) × C) ((A × B) × C) ℂ)
    (hrho : IsDensityMatrix rho) :
    let ab := traceRight rho
    informationalDistance ab = informationalDistance (swapState ab) ∧
    informationalDistance rho ≥ informationalDistance (traceRight
      (fun p q : (A × C) × B =>
        rho ((p.1.1, p.2), p.1.2) ((q.1.1, q.2), q.1.2))) ∧
    (0 ≤ informationalDistance ab ∧ informationalDistance ab ≤ 2) ∧
    (∀ (J : Type) [Fintype J] [DecidableEq J] (F : Superop (A × B) J),
      IsChannel F → traceNorm (F ab - F (jointMarginalProduct ab)) ≤ informationalDistance ab) ∧
    informationalDistance ab ≤ Real.sqrt (2 * jointMutualInfoBits ab) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
