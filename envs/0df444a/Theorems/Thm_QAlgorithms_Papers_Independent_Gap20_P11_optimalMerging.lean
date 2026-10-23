-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P11_optimalMerging
-- name    : QAlgorithms.Papers.Independent.Gap20.P11.optimalMerging
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:15:15.952644+00:00
-- url     : https://prove2.me/theorems/62fa9c09-f360-43bf-8fd7-1e393855acff
-- title:
--   Optimal state merging has signed cost S(A|B)
-- statement:
--   Let $\rho_{AB}$ be a density operator on finite, nonzero-dimensional complex registers $A$ and $B$. Entropies are measured in bits. Consider independent copies of this source, local operations and unlimited classical communication, and codes that depend only on $\rho_{AB}$. The inaccessible purifying reference is left untouched. If a block protocol receives $k_n$ Bell pairs and returns $\ell_n$ Bell pairs, its signed entanglement cost is the real difference $k_n-\ell_n$. The joint output, including those returned pairs, must converge in trace norm to the reconstructed pure source at Bob tensored with the Bell resource.
--
--   A real rate $e$ is achievable when every positive error tolerance and rate slack can be met at every sufficiently large positive blocklength with net cost at most $n(e+\delta)$. Then
--
--   $$
--   e\text{ is achievable}\quad\Longleftrightarrow\quad e\ge S(A\mid B)_\rho=S(\rho_{AB})-S(\rho_B).
--   $$
--
--   There is a one-way construction attaining this threshold. For arbitrarily small positive slack it consumes at most $n(\max\{S(A\mid B),0\}+\delta)$ pairs and returns at least $n(\max\{-S(A\mid B),0\}-\delta)$ pairs, with the same net-cost bound. If $S(A\mid B)<0$, no initial Bell pairs are required. Consumed pairs may be distributed by sending qubits, and teleportation converts them into source transfer using the allowed classical communication.
--
--   This gives the operational meaning of negative conditional entropy: merging can transfer the source while producing entanglement for future communication.
-- source:
--   Quantum information can be negative, arXiv:quant-ph/0505062v1, PDF p. 2, Unnumbered main result: optimal quantum state merging and negative information

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P11

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1–3, main result and (1): the optimal LOCC merging cost is precisely
S(A|B), including its negative part. The second conjunct gives an actual one-way
construction, with no seed entanglement in the strictly negative regime.
Source-sketch discrepancies (p.3): the printed S(A)>S(AB) is replaced by
S(B)>S(AB), as follows directly from (1); exactly S(A|B) added ebits
would give zero conditional entropy, so the coding assertion uses positive
rate slack instead of the sketch's strict inequality at equality. -/
theorem optimalMerging {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    (∀ rate : ℝ, MergingAchievable rho rate ↔ conditionalEntropy rho ≤ rate) ∧
    (∃ c : ℝ, MergingConstruction rho c (conditionalEntropy rho)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P11

end
