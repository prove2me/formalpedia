-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_partial_tests_upper_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.partial_tests_upper_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:02:23.958276+00:00
-- url     : https://prove2.me/theorems/2ec95d77-35fb-452d-a9af-10142660f984
-- title:
--   Partial-test upper bounds and exact certification
-- statement:
--   Fix $d,k\ge1$, a physical protocol class, and a linear unitary-channel target $f$. Let $B$ be any finite set of unitary test inputs. Suppose $(p,S,F)$ is a feasible maximizer with only those tests. Then every universally achievable coefficient $q$ satisfies
--
--   $$q\le p.$$
--
--   If the same success matrix $S$ also passes every test in an exact basis of the full repeated-unitary Choi span, then $p$ itself is universally achievable and hence optimal. Both branches remain physical throughout.
--
--   This separates a relaxation bound from a certificate: the final full-basis verification is indispensable.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 7, III, Eq. (20)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.7, Eq. (20): partial tests relax the optimization; an attained relaxed
solution that passes a full exact basis certifies global optimality. -/
theorem partial_tests_upper_bound {d k n : ℕ} (hd : 0 < d) (hk : 0 < k)
    (c : ProtocolClass) (f : Op (Fin d × Fin d) →ₗ[ℂ] Op (Fin d × Fin d))
    (hf : UnitaryLinearTarget f) (B : Fin n → Matrix.unitaryGroup (Fin d) ℂ)
    (p : ℝ) (S F : Op (ProcessBasis (uniformWires d k)))
    (hp : TestedFeasible (k := k) c f B p S F)
    (hmax : ∀ q, (∃ T G, TestedFeasible (k := k) c f B q T G) → q ≤ p) :
    (∀ q, Attainable c d k (fun U => f (gateChoi (U : Op (Fin d)))) q → q ≤ p) ∧
    (∀ (m : ℕ) (C : Fin m → Matrix.unitaryGroup (Fin d) ℂ),
      IsUnitaryBasis d k m C →
      (∀ i, evaluateOracleSlots S (repeatedChoi k (C i)) = (p : ℂ) • f (gateChoi (C i : Op (Fin d)))) →
      Attainable c d k (fun U => f (gateChoi (U : Op (Fin d)))) p) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
