-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_pureFixedPoint_protects
-- name    : QAlgorithms.Papers.Independent.Information100.P07.pureFixedPoint_protects
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:34:15.861933+00:00
-- url     : https://prove2.me/theorems/25fd9850-ba30-4da2-bdc6-b7998a3a8ecb
-- title:
--   Lemma S1: pure fixed point protects its whole Schmidt rectangle
-- statement:
--   Let $\Omega$ be a separable CPTP channel fixing a normalized pure state $|\psi\rangle\langle\psi|$ of Schmidt rank two. Let $U,V$ be its two Schmidt support spaces, and $L=U\otimes V$. For every finite product Kraus representation $(K_i)$ of $\Omega$, there are probabilities $p_i\ge0$, summing to one, and product unitaries $W_i$ on $L$ such that
--   $$K_i x=\sqrt{p_i}W_i x\quad(x\in L),\qquad\Omega(P_L)=P_L.$$
--   The restrictions have image in $L$; at $p_i=0$ they vanish on all of $L$.
--
--   This protects the entire Schmidt rectangle of a pure fixed point.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 9, Lemma S1: pure fixed point protects its whole Schmidt rectangle

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF p.9, Lemma S1: every finite product Kraus representation. -/
theorem pureFixedPoint_protects (psi : Space) (hpsi : IsState psi)
    (hsr : (traceRight (pureDensity psi)).rank = 2)
    (Phi : Superop (Fin 3 × Fin 3) (Fin 3 × Fin 3))
    (hPhi : SeparableChannel Phi) (hfix : Phi (pureDensity psi) = pureDensity psi) :
    (∀ (m : ℕ) (K : Fin m → Joint), IsKrausFamily K → (∀ i, IsProduct (K i)) →
      (∀ X, Phi X = krausApply K X) →
      ∃ p : Fin m → ℝ, ProductProtects K (support (traceRight (pureDensity psi)))
        (support (traceLeft (pureDensity psi))) p) ∧
    Phi (schmidtRectangle psi) = schmidtRectangle psi := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
