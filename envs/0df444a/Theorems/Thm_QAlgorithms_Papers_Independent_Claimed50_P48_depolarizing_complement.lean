-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_depolarizing_complement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.depolarizing_complement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:55:49.926168+00:00
-- url     : https://prove2.me/theorems/20201a6f-9a31-4b38-9c85-dc4b227a216b
-- title:
--   Explicit depolarizing complement and its covariance
-- statement:
--   Let $d\ge2$ and $0\le t\le d^2/(d^2-1)$. The depolarizing map $\Phi_t(X)=(1-t)X+(t/d)\operatorname{Tr}(X)I$ has a complementary channel $\Psi_t(X)=S(X\otimes I)S$, where $\Omega=d^{-1/2}\sum_j e_j\otimes e_j$ and
--
--   $$S=\sqrt{t/d}\,I+\sqrt d\left[-\frac{\sqrt t}{d}+\sqrt{1-t\frac{d^2-1}{d^2}}\right]|\Omega\rangle\langle\Omega|.$$
--
--   Both maps are channels on the entire displayed parameter interval. For every unitary $U$ and every operator $X$,
--
--   $$\Psi_t(UXU^*)=(U\otimes\overline U)\Psi_t(X)(U\otimes\overline U)^*.$$
--
--   The parameter $t$ is the noise parameter, independent of any Schatten exponent. This retains the source's upper CP endpoint beyond one.
--
--   The receiver is globally unitarily covariant on all operators:
--
--   $$\Phi_t(UXU^*)=U\Phi_t(X)U^*.$$
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 8, Explicit depolarizing complement and its covariance

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- PDF pp.8–9: the whole CP interval, including t>1, the computed S,
receiver covariance with U, and complement covariance with U tensor conjugate U. -/
theorem depolarizing_complement (d : ℕ) (hd : 2 ≤ d) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) :
    let hpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hd
    IsChannel (QuditFidelity.depolarizingMap d hpos t) ∧ IsChannel (depolarizingComplement d hpos t) ∧
    CPComplementary (QuditFidelity.depolarizingMap d hpos t) (depolarizingComplement d hpos t) ∧
    (∀ (U : Matrix.unitaryGroup (Fin d) ℂ) rho,
      depolarizingComplement d hpos t ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
      ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ).map conj) *
        depolarizingComplement d hpos t rho *
        ((U : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (U : Matrix (Fin d) (Fin d) ℂ).map conj)ᴴ) ∧
    (∀ (U : Matrix.unitaryGroup (Fin d) ℂ) rho,
      QuditFidelity.depolarizingMap d hpos t
          ((U : Matrix (Fin d) (Fin d) ℂ) * rho * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
        (U : Matrix (Fin d) (Fin d) ℂ) * QuditFidelity.depolarizingMap d hpos t rho *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
