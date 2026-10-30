-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_firmSubadditivity_implies_subadditivity
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.firmSubadditivity_implies_subadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:49:20.763771+00:00
-- url     : https://prove2.me/theorems/c51dba9b-8375-46f4-b629-30d622ab1b14
-- title:
--   Firm subadditivity strengthens subadditivity
-- statement:
--   Let $S_K$ be a concave family of finite-dimensional quantum entropies, depending only on the multiset of nonzero eigenvalues and vanishing on pure states. Define $I_K(a:b)=S_K(\rho_a)+S_K(\rho_b)-S_K(\rho_{ab})$. For a finite POVM $P_a$ on $a$, let $\chi_K(P_a,b)$ be the entropy of $\rho_b$ minus the probability-weighted entropies of its normalized conditional states.
--
--   If $S_K$ is firmly subadditive, meaning $\chi_K(P_a,b)\le I_K(a:b)$ for every state and POVM in every finite positive dimension, then it is subadditive. Moreover, the strengthening term is always nonnegative:
--
--   $$
--   S_K(\rho_{ab})\le S_K(\rho_a)+S_K(\rho_b),\qquad \chi_K(P_a,b)\ge0.
--   $$
--
--   The nonnegativity conclusion holds for every such state and measurement, independently of whether FSA holds. It explains why FSA strengthens ordinary subadditivity.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 2, Proposition 1 (§III): FSA implies SA

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF p.2, Proposition 1: FSA implies SA, and the strengthening term is nonnegative. -/
theorem firmSubadditivity_implies_subadditivity (S : EntropyFunction) (hS : IsEntropy S) :
    (FirmlySubadditive S → SubadditiveEntropy S) ∧
    (∀ {A B J : Type} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype J] [DecidableEq J] [Nonempty J]
      (rho : Matrix (A × B) (A × B) ℂ) (P : J → Matrix A A ℂ),
      IsDensityMatrix rho → IsPOVM P → 0 ≤ measurementHolevo S rho P) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end
