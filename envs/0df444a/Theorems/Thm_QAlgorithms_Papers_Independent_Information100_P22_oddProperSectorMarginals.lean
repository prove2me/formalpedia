-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_oddProperSectorMarginals
-- name    : QAlgorithms.Papers.Independent.Information100.P22.oddProperSectorMarginals
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:15:57.821241+00:00
-- url     : https://prove2.me/theorems/5c704a18-a1d4-4427-8f9a-6f5bedfad43b
-- title:
--   §V D / Eq.(S69), unnumbered: proper sector marginals
-- statement:
--   Let $m\ge2$ be odd, $k\ge1$, and suppose a normalized pure resource satisfies Eq.(3) for fixed distinct encoder axes. For any sector $j$ and every proper subset $J$ of its $m$ signal qubits,
--   $$\operatorname{Tr}_{S\setminus J}(\rho_S)=I_J/2^{|J|}.$$
--   The empty subset is included and has scalar density one. The entire sector is excluded. These are initial resource marginals, not encoded-input marginals; the result isolates the complete-sector nature of every nonidentity allowed correlation.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 43, §V D / Eq.(S69), unnumbered: proper sector marginals

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Eq.(S69), PDF pp.14,43: initial resource marginal on any proper subset of one sector. -/
theorem oddProperSectorMarginals (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) (hodd : Odd m)
    (P Q : Axis) (hPQ : P ≠ Q)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R)
    (hc : ResourceCriterion P Q (rhoS R)) (j : Fin k) (J : Finset (Wires m k))
    (hJ : J ⊂ Finset.univ.filter (fun w => w.1 = j)) :
    marginal J (rhoS R) = mixed (J → Bool) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
