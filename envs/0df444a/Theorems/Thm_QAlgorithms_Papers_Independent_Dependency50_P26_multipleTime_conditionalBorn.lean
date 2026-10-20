-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_multipleTime_conditionalBorn
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.multipleTime_conditionalBorn
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:46:49.647497+00:00
-- url     : https://prove2.me/theorems/5ad79be8-9384-4c03-9b81-74dce370983f
-- title:
--   §VI Eqs.(92)–(94): multi-time conditional Born rule
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. For $N\ge1$, choose unit preparation vectors $\Psi_j$ on each input and unit postselection vectors $\Phi_{j+1}$ on each output. Let $S$ be their product-history operator from Eq.(92), and let the measurement histories be $R_i=\sum_a|K_{ia}\rangle\rangle\langle\langle K_{ia}|$ forming a generalized instrument. Write $v$ for the coordinate vector of $S=|v\rangle\langle v|$, where each output factor is complex-conjugated. If the total postselection weight is positive, then
--
--   $$
--   p(i\mid S)=\frac{\operatorname{Re}\operatorname{Tr}(SR_i^T)}{\sum_j\operatorname{Re}\operatorname{Tr}(SR_j^T)}=\frac{\sum_a|\sum_x v_x(K_{ia})_x|^2}{\sum_{j,a}|\sum_xv_x(K_{ja})_x|^2}.
--   $$
--
--   The conditional weights are nonnegative and sum to one. No conditional probability is asserted at zero denominator. The coordinate amplitude is the contraction $\langle\Phi_1|\cdots\langle\Phi_N|K_{ia}|\Psi_0\rangle\cdots|\Psi_{N-1}\rangle$.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 20, §VI Eqs.(92)–(94): multi-time conditional Born rule

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.20, Eqs.(92)–(94): both the Kraus-amplitude and trace forms, and a normalized
conditional distribution. Conditioning on successful postselection requires positive denominator. -/
theorem multipleTime_conditionalBorn (s : Signature) (n k q : ℕ) (hn : 0 < n)
    (prep : (j : ℕ) → Fin (s.input j) → ℂ)
    (post : (j : ℕ) → Fin (s.output j) → ℂ)
    (hprep : ∀ j < n, (∑ a, Complex.normSq (prep j a)) = 1)
    (hpost : ∀ j < n, (∑ a, Complex.normSq (post j a)) = 1)
    (K : Fin k → Fin q → Basis s n → ℂ)
    (hK : CombInstrument s n k (fun i => ∑ a, rankOne (K i a)))
    (hden : 0 < ∑ i, QAlgorithms.effectProb (∑ a, rankOne (K i a)).transpose
      (rankOne (multiTimeVector s prep post n))) :
    let R := fun i => ∑ a, rankOne (K i a)
    let S := rankOne (multiTimeVector s prep post n)
    (∀ i, conditionalBorn R S i =
      (∑ a, Complex.normSq (∑ x, multiTimeVector s prep post n x * K i a x)) /
      (∑ j, ∑ a, Complex.normSq (∑ x, multiTimeVector s prep post n x * K j a x))) ∧
    (∀ i, 0 ≤ conditionalBorn R S i) ∧ (∑ i, conditionalBorn R S i) = 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
