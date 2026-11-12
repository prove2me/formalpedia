-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_unramified_lifting
-- name    : QuantumGroupCodes836.Addressability.unramified_lifting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:12:30.444263+00:00
-- url     : https://prove2.me/theorems/67315d83-35a4-4c74-8f9f-8980b38235e2
-- title:
--   Theorem 4.4 — unramified lifting and free Riemann–Roch spaces
-- statement:
--   Let $F/k$, $P$, $D$, $m$ and $\eta$ satisfy the standing hypotheses of §4.1.2: $P$ sums distinct rational places, $D$ is disjoint from $P$, $2g-2<\deg D<n$, $m>0$, and $\eta$ has simple poles at $P$ with $(m+1)D\le P+(\eta)$. There is a separable unramified extension with full constants $k_2$ of size $|k|^2$, abelian over the constant extension $k_2F$, with group $G$ satisfying
--
--   $$|G|\ge(\sqrt{|k|}-1)^{2g(F)}.$$
--
--   The conorm $\widetilde P$ enumerates $n|G|$ rational places. Both conorm divisors are invariant; $\deg\widetilde D=|G|\deg D$ lies strictly between $2g(\widetilde F)-2$ and $n|G|$. The space $L(\widetilde D)$ is free of rank $\deg D-g+1$. Cotrace retains simple poles and the full divisor inequality. All six numbered conclusions are retained.
--
--   Differences from the source:
--   - encoding: function fields, places, divisors and differentials → finite extensions with full constants, valuation-ring places, finitely supported divisors and Kähler differentials; reason: no separating chart, lifting existence or parameter bound is assumed; regular differential dimension computes genus
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Theorem 4.4, pp.15–16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Lifting

set_option autoImplicit false

namespace QuantumGroupCodes836.Addressability

theorem unramified_lifting {k : Type} [Field k] [Fintype k] (F : FunctionFieldData k)
    (P : EvaluationData F) (D : Divisors F) (m : ℕ) (η : KaehlerDifferential k F.carrier)
    (h : AGAssumptions P D m η) :
    ∃ L : LiftData F,
      Fintype.card L.constants = (Fintype.card k)^2 ∧
      Unramified L.extension ∧ SeparableExtension L.extension ∧
      GaloisOverConstantSubfield L ∧ IsAbelian (G := L.group) ∧
      (Real.sqrt (Fintype.card k) - 1) ^ (2 * genus F) ≤ (Nat.card L.group : ℝ) ∧
      evaluationDivisor L.evaluation = conorm L.extension (evaluationDivisor P) ∧
      L.evaluation.n = P.n * Nat.card L.group ∧
      AlgebraicCurve.Divisor.degree (conorm L.extension D) =
        AlgebraicCurve.Divisor.degree D * Nat.card L.group ∧
      2 * (genus L.upstairs : ℤ) - 2 < AlgebraicCurve.Divisor.degree (conorm L.extension D) ∧
      AlgebraicCurve.Divisor.degree (conorm L.extension D) < P.n * Nat.card L.group ∧
      (∀ σ : L.group, σ.val • conorm L.extension D = conorm L.extension D ∧
        σ.val • evaluationDivisor L.evaluation = evaluationDivisor L.evaluation) ∧
      RRFree L D (AlgebraicCurve.Divisor.degree D - genus F + 1).toNat ∧
      (∀ i, (L.evaluation.places i).ordDifferential (cotrace L.extension η) = -1) ∧
      (m + 1) • conorm L.extension D ≤ evaluationDivisor L.evaluation +
        differentialDivisor (cotrace L.extension η) := by sorry

end QuantumGroupCodes836.Addressability
