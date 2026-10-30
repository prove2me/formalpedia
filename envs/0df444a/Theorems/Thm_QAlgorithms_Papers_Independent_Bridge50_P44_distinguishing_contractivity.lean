-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_distinguishing_contractivity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.distinguishing_contractivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:19:55.615301+00:00
-- url     : https://prove2.me/theorems/dddc8917-6af5-441a-a9b1-e2da68b981fc
-- title:
--   C.1: closure implies distinguishing contractivity
-- statement:
--   Let a nonempty class of abstract binary-output tests act on compatible resources, and let $D(R)$ denote each test's actual binary execution law. Define the signed distinguishing advantage
--
--   $$d(R,S)=\sup_D\bigl(\Pr[D(R)=1]-\Pr[D(S)=1]\bigr).$$
--
--   If the class is closed under precomposition with every converter $\alpha$ and with every parallel resource context $T$, preserving those execution laws on every input resource, then
--
--   $$d(\alpha R,\alpha S)\le d(R,S),\qquad d(R\parallel T,S\parallel T)\le d(R,S).$$
--
--   The supremum is bounded because the execution laws are probability laws. This abstract closure theorem neither assumes optimal-test attainment nor infers symmetry of an arbitrary restricted test class.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 46, C.1: closure implies distinguishing contractivity

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.45--46, Appendix C.1: closure under precomposition gives both
converter and parallel-context contractivity for the signed supremum. No
symmetry or complement closure of a restricted distinguisher class is inferred. -/
theorem distinguishing_contractivity {R D C : Type} [Nonempty D]
    (run : D → R → PMF Bool) (attach : C → R → R) (parallel : R → R → R)
    (hattach : ∀ c, ClosedTests run (attach c))
    (hparallel : ∀ t, ClosedTests run (fun r => parallel r t)) (r s : R) :
    (∀ c, distinguishingAdvantage run (attach c r) (attach c s) ≤ distinguishingAdvantage run r s) ∧
    (∀ t, distinguishingAdvantage run (parallel r t) (parallel s t) ≤ distinguishingAdvantage run r s) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
