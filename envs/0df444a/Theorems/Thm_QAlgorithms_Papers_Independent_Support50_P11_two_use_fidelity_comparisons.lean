-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_two_use_fidelity_comparisons
-- name    : QAlgorithms.Papers.Independent.Support50.P11.two_use_fidelity_comparisons
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:14:20.400336+00:00
-- url     : https://prove2.me/theorems/747a5c23-fe15-45da-a121-f5ca46b56690
-- title:
--   §VII.B, Fig.6: two-use finite-block fidelity comparisons
-- statement:
--   Fix exactly two parallel uses $\mathcal N=(\mathcal W^{(3,1)})^{\otimes2}$ of the qutrit Werner–Holevo channel. The finite-block optimal fidelities obey
--   $$F^{\mathrm{NS}}(\mathcal N,3)=1,\qquad F^{\mathrm{NS}}(\mathcal N,K)<F^{\mathrm{PPTp}}(\mathcal N,K)\quad(K\ge4).$$
--   There is a positive integer $K$ for which
--   $$F^{\mathrm{NS}\cap\mathrm{PPTp}}(\mathcal N,K)<\min\{F^{\mathrm{NS}}(\mathcal N,K),F^{\mathrm{PPTp}}(\mathcal N,K)\},$$
--   and for every integer $K\ge9$,
--   $$F^{\mathrm{NS}\cap\mathrm{PPTp}}(\mathcal N,K)=F^{\mathrm{NS}}(\mathcal N,K).$$
--   These are the stated two-use comparisons; the strict intersection improvement is retained existentially rather than assigning uncertified rational values from the graph.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 11, §VII.B, Fig.6: two-use finite-block fidelity comparisons

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.11, section VII.B, Fig.6: the two-use finite-block comparisons.
The strict intersection improvement is existential, with no invented graph values. -/
theorem two_use_fidelity_comparisons :
    let N := piSuperop (fun _ : Fin 2 => wernerHolevoChannel 3 1)
    optimalCodeFidelity .NS N 3 = 1 ∧
    (∀ K : ℕ, 4 ≤ K → optimalCodeFidelity .NS N K < optimalCodeFidelity .PPTp N K) ∧
    (∃ K : ℕ, 0 < K ∧ optimalCodeFidelity .both N K < min (optimalCodeFidelity .NS N K) (optimalCodeFidelity .PPTp N K)) ∧
    (∀ K : ℕ, 9 ≤ K → optimalCodeFidelity .both N K = optimalCodeFidelity .NS N K) := by sorry

end QAlgorithms.Papers.Independent.Support50.P11

end
