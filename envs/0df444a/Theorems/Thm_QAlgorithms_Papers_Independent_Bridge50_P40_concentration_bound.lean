-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_concentration_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.concentration_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:00:43.417853+00:00
-- url     : https://prove2.me/theorems/077d8b32-14bd-449a-9339-3560effd6fc6
-- title:
--   Finite-block strong converse for entanglement concentration
-- statement:
--   All registers are finite and nonempty. Density operators have trace one, pure states are normalized, all entropies and logarithms are in base two, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Write $S_a$ for Petz Rényi entropy, with support projection at order zero and the von Neumann limit at order one; $S_\infty(\rho)=-\log_2\lambda_{\max}(\rho)$.
--
--   Let $\psi^{AB}$ be a normalized pure source. Let $n\ge1$, $L\ge1$, and let an LOCC operation $\mathcal M:A^n:B^n\to A_1:B_1$ act on $\psi^{\otimes n}$ with no supplied entanglement, with target $\Phi_L$. If $0\le F\le1$ is at most the actual root fidelity with that target, then for $1<a\le2$,
--
--   $$
--   F\le2^{\frac{n(a-1)}{2a}\left[S_{2-a}(A)_\psi-\frac{\log_2L}{n}\right]}.
--   $$
--
--   The yield occurs with a minus sign, so a yield above the source entropy forces fidelity decay. Order zero at $a=2$ uses support rank.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 11, Theorem 11, equation (58)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.11, Theorem 11, (58): concentration yield has the opposite rate
sign. The input has n source copies and no supplied entanglement resource. -/
theorem concentration_bound {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : IsState psi)
    (n L : ℕ) (hn : 0 < n) (hL : 0 < L)
    (M : Superop ((Fin n → A) × (Fin n → B)) (Fin L × Fin L)) (hM : IsLOCC M)
    (F a : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hF : F ≤ rootFidelity (M (pureDensity (concentrationInput psi n))) (pureDensity (bell (Fin L))))
    (ha : 1 < a) (ha2 : a ≤ 2) :
    F ≤ (2 : ℝ) ^ ((n : ℝ) * (a - 1) / (2 * a) *
      (renyiEntropy (2 - a) (traceRight (pureDensity psi)) - Real.logb 2 L / (n : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
