-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_multipartite_assistance
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.multipartite_assistance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:37:01.870678+00:00
-- url     : https://prove2.me/theorems/999767bd-c564-4afc-b54b-9a1fa0ac5cdf
-- title:
--   Theorem 3: multipartite min-cut assistance and single-turn helpers
-- statement:
--   Let $m\ge2$, let $A,B$ be distinct parties, and let $\psi$ be a normalized pure state on $m$ nonzero finite-dimensional local spaces. All helpers act individually locally; quantum messages and additional shared entanglement are unavailable. For a helper subset $T$, let $S(AT)$ be the entropy in bits across the cut separating $AT$ from $B$ and the remaining helpers. Then
--
--   $$R_{\rm LOCC}=R_{\rm single\ turn}=\min_{T\subseteq\{C_1,\ldots,C_{m-2}\}}S(AT).$$
--
--   For either protocol class, the nonnegative achievable rates are exactly the interval from zero to this value. In the single-turn class each helper measures once, broadcasts its result, and disposes of its remaining quantum system; later helper measurements may depend on earlier results, and the receivers may finish by LOCC. The minimum is attained over a nonempty finite set of cuts. With no helpers, the sole cut is $A|B$; zero-cut and product states have zero yield. The paper proves the four-party case directly and explicitly attributes general achievability to [20]. This supplies the individually local finite-helper assistance interface.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 2, Theorem 3: multipartite min-cut assistance and single-turn helpers

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P93

namespace QAlgorithms.Papers.Independent.Intake100.P93

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; no chunk-local aliases.

open Information100.P21 (Op)

open Information100.P08 (PureEnsemble)

open Dependency50.P07 (bipartiteProduct)

open Information100.P67 (receiverChannel)

open Support50.P11 (choiState)

/-- PDF pp.2,7--8,10, Theorem 3: all m≥2, including no helpers. The bound
ranges over every separating cut and is attained with individually local
single-turn helpers. The paper proves m=4 directly and attributes general
achievability to [20]; the full assertion is explicitly stated here. -/
theorem multipartite_assistance {m : ℕ} (hm : 2 ≤ m) {d : Fin m → ℕ}
    (hd : ∀ i, 0 < d i) (a b : Fin m) (hab : a ≠ b)
    (psi : EuclideanSpace ℂ (AssistanceBasis d)) (hpsi : ‖psi‖ = 1) :
    (∃ s : Finset (Fin m), cutMinimum (pureDensity psi) a b =
      partyEntropy (pureDensity psi) (insert a (s.erase b))) ∧
    ∀ r : ℝ,
      (AssistedYield (pureDensity psi) .locc a b 0 r ↔
        0 ≤ r ∧ r ≤ cutMinimum (pureDensity psi) a b) ∧
      (AssistedYield (pureDensity psi) .singleTurn a b 0 r ↔
        0 ≤ r ∧ r ≤ cutMinimum (pureDensity psi) a b) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
