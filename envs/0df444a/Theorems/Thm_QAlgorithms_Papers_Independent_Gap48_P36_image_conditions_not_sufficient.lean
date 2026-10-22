-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_image_conditions_not_sufficient
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.image_conditions_not_sufficient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:09:06.58777+00:00
-- url     : https://prove2.me/theorems/516c4236-9c50-4d6e-a3e4-ded7ee676751
-- title:
--   Unnumbered: conditions of Theorem 12 are not sufficient
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. There exist a positive dimension $d$, a phase-closed unitary orthogonal basis $T$, and a density $\gamma$ on dimension $d^2$ satisfying
--
--   $$
--   (d\gamma)^2=d\gamma,\quad\operatorname{rank}(d\gamma)=d,\quad\gamma_{mm}=d^{-2},\quad |\gamma_{mn}|\le d^{-2},
--   $$
--
--   and with $d^3|\gamma_{mn}|^2$ doubly stochastic, but with $\gamma\ne N^{C,T}(|\psi\rangle\langle\psi|)$ for every unit input $\psi$. Here $N^{C,T}$ uses Kraus matrices $T_m/d$. This is an existential failure of sufficiency, not a claim in every dimension.
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 20, Unnumbered: conditions of Theorem 12 are not sufficient

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P36

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Claimed50.P48

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P03 (convexRoof)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D E K L A2 B2 C2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

variable [Fintype L] [DecidableEq L] [Fintype A2] [DecidableEq A2]

variable [Fintype B2] [DecidableEq B2] [Fintype C2] [DecidableEq C2]

/-- Unnumbered non-sufficiency assertion, PDF p.20: existence, not every dimension or basis. -/
theorem image_conditions_not_sufficient :
    ∃ d : ℕ, ∃ hd : 0 < d,
      ∃ T : UnitaryBasis (Fin d) (Fin (d^2)), PhaseClosed T ∧
      ∃ gamma : Matrix (Fin (d^2)) (Fin (d^2)) ℂ,
        ImageConditions d gamma ∧ gamma ∉ pureNoisyImage T.matrix := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
