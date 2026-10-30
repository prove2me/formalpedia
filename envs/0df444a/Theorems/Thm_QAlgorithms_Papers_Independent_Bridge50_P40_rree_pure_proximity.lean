-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_rree_pure_proximity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.rree_pure_proximity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:57:52.18699+00:00
-- url     : https://prove2.me/theorems/ec38850f-911f-4094-a238-31b6b22511b0
-- title:
--   RREE lower bound from proximity to a pure state
-- statement:
--   All registers are finite and nonempty. Density operators have trace one, pure states are normalized, all entropies and logarithms are in base two, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Write $S_a$ for Petz Rényi entropy, with support projection at order zero and the von Neumann limit at order one; $S_\infty(\rho)=-\log_2\lambda_{\max}(\rho)$.
--
--   Write $E_{\rm RE}^{(a)}(A:B)_\rho=\inf_{\sigma\in\mathrm{Sep}(A:B)}D_a(\rho\|\sigma)$ for the relative entropy of entanglement formed from support-aware Petz divergence.
--
--   Let $\rho^{AB}$ be a density operator and $\psi^{AB}$ a normalized pure state, with $0\le F\le1$ and $F\le F(\psi,\rho)$. For $1<a\le2$,
--
--   $$
--   F\le2^{\frac{a-1}{2a}\left[E_{\rm RE}^{(a)}(A:B)_\rho-S_{1/(2-a)}(A)_\psi\right]}.
--   $$
--
--   At $a=2$ the entropy is $S_\infty(A)_\psi$. This exponentiated form is equivalent to (24) for positive $F$ and also includes $F=0$.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 7, Lemma 6, equation (24)

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

/-- PDF p.7, Lemma 6, (24): exponentiated form retains F=0; at a=2 the
pure marginal entropy is the infinite-order entropy, not entropy of order zero. -/
theorem rree_pure_proximity {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : IsState psi)
    (F a : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hF : F ≤ rootFidelity (pureDensity psi) rho) (ha : 1 < a) (ha2 : a ≤ 2) :
    F ≤ (2 : ℝ) ^ ((a - 1) / (2 * a) *
      (rree a rho - reciprocalEntropy a (traceRight (pureDensity psi)))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
