-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P34_formationContinuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P34.formationContinuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:04:11.835874+00:00
-- url     : https://prove2.me/theorems/69e61d80-8bea-4b93-954e-64be15d0a484
-- title:
--   Formation continuity with the proof-intended purification distance
-- statement:
--   Let $A$ and $B$ be finite complex systems of positive dimensions $d$ and $d'$, and let $\rho,\sigma$ be density matrices on $A\otimes B$. Write $E_F$ for the minimum average bit entropy of the $A$ reduction over all finite pure-state decompositions. Let $F(\rho,\sigma)=\operatorname{Tr}\sqrt{\sqrt\rho\,\sigma\sqrt\rho}$ be root fidelity and put $\Delta=2\sqrt{1-F(\rho,\sigma)^2}$. Define $\eta(x)=-x\log_2x$, with $\eta(0)=0$, and let $e=\exp(1)$. If $\Delta\le1/e$, then
--
--   $$
--   |E_F(\rho)-E_F(\sigma)|\le\min\{5\log_2d+4\log_2d',\,5\log_2d'+4\log_2d\}\,\Delta+2\eta(\Delta).
--   $$
--
--   The same left side is also at most $9\log_2(\max\{d,d'\})\Delta+2\eta(\Delta)$. These bounds quantify finite-dimensional formation continuity, allowing the source's interchange of the two systems.
--
--   **Formalization Note** This is the explicitly corrected, proof-intended statement: printed (10) uses $2\sqrt{1-F}$, which is incompatible with the pure-state identity used in its proof. The theorem does not certify the literal printed-distance version of (18).
-- source:
--   Continuity bounds for entanglement, arXiv:quant-ph/9908086v2, PDF p. 3, Main result: entanglement-of-formation continuity, (18), with the distance used by its proof

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P34

attribute [local instance] Classical.propDecidable Classical.decEq

-- Accepted definition providers, authorized by the independent-paper workflow.

open QAlgorithms.Papers.Independent.Information100.P08 (formation bellVector)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Support50.P42 (outcomeEntropy)

-- The supplied diagnostic timed out while elaborating the remote-control statement.

set_option maxHeartbeats 800000

/-- PDF p.3, (18), with the explicit proof-intended correction described above.
Exchanging A and B gives the minimum coefficient; the stated 9 log(max) bound
is retained as well. This does not assert the literal printed-distance claim. -/
theorem formationContinuity {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho sigma : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsmall : purificationDistance rho sigma ≤ 1 / Real.exp 1) :
    |formation rho - formation sigma| ≤
      min (5 * Real.logb 2 (Fintype.card A) + 4 * Real.logb 2 (Fintype.card B))
        (5 * Real.logb 2 (Fintype.card B) + 4 * Real.logb 2 (Fintype.card A)) *
        purificationDistance rho sigma +
        2 * (-(purificationDistance rho sigma) * Real.logb 2 (purificationDistance rho sigma)) ∧
    |formation rho - formation sigma| ≤
      9 * Real.logb 2 (max (Fintype.card A) (Fintype.card B)) *
        purificationDistance rho sigma +
        2 * (-(purificationDistance rho sigma) * Real.logb 2 (purificationDistance rho sigma)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P34

end
