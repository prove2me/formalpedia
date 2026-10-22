-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P36_qc_pauli_powers
-- name    : QAlgorithms.Papers.Independent.Gap48.P36.qc_pauli_powers
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:09:50.353135+00:00
-- url     : https://prove2.me/theorems/911a587d-00f6-4248-806d-73a666ebb2ba
-- title:
--   Example 4: QC Pauli channels attain the bound and are tensor-power multiplicative
-- statement:
--   All Hilbert spaces have positive finite dimension. Channels are completely positive and trace preserving; conjugates use the same normalized pure-environment dilation. Use $X|k\rangle=|k+1\bmod d\rangle$, $Z|k\rangle=e^{2\pi ik/d}|k\rangle$, $W_{jk}=X^jZ^k$, and labels $(j,k)\in(\mathbb Z/d\mathbb Z)^2$. Write $\nu_p(\Phi)=\sup_\rho\|\Phi(\rho)\|_p$ and $S_{\min}(\Phi)=\inf_\rho S(\Phi(\rho))$, with density inputs, Schatten norm, and von Neumann entropy. Let $a_{jk}=a_j\ge0$ be independent of $k$ and satisfy $d\sum_j a_j=1$. Then
--
--   $$
--   \begin{gathered}\Phi(\rho)=d\sum_j a_jX^j\rho_{\mathrm{diag}}X^{-j},\qquad\nu_p(\Phi)=\left(\sum_j(da_j)^p\right)^{1/p},\\\nu_p(\Phi^{\otimes m})=\nu_p(\Phi)^m\quad(p\ge1,\ m\ge1).\end{gathered}
--   $$
--
--   The matrix $\rho_{\mathrm{diag}}$ keeps the computational diagonal. The channel admits rank-one Kraus matrices, hence is entanglement breaking, and attains the sorted block bound for every labeled sorted arrangement. The factor $d$ corrects the last expression of (71).
-- source:
--   Properties of Conjugate Channels with Applications to Additivity and Multiplicativity, arXiv:quant-ph/0509126v3, PDF p. 24, Example 4: QC Pauli channels attain the bound and are tensor-power multiplicative

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

/-- Example 4, PDF pp.24–25: normalized QC channel, sharp bound and all positive powers.
Correction to (71): summing the clock conjugations gives d times the diagonal. -/
theorem qc_pauli_powers (d : ℕ) [NeZero d] (a : ZMod d → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : (d : ℝ) * ∑ j, a j = 1)
    (p : ℝ) (hp : 1 ≤ p) :
    let Phi := randomUnitary (finWeyl d) (fun jk => a jk.1)
    (∀ rho, Phi rho = (d : ℂ) •
      (∑ j : ZMod d, (a j : ℂ) •
        (finWeyl d (1,0) ^ j.val * Matrix.diagonal (fun i => rho i i) * (finWeyl d (1,0) ^ j.val)ᴴ))) ∧
    nu (ENNReal.ofReal p) Phi = Real.rpow (∑ j, Real.rpow ((d : ℝ) * a j) p) (1 / p) ∧
    HasRankOneKraus Phi ∧
    (∀ e : (Fin d × Fin d) ≃ WeylLabel d, SortedRows (fun jk => a jk.1) e →
      nu (ENNReal.ofReal p) Phi = blockBound p (fun jk => a jk.1) e) ∧
    (∀ m : ℕ, 1 ≤ m → nu (ENNReal.ofReal p) (piSuperop (fun _ : Fin m => Phi)) =
      nu (ENNReal.ofReal p) Phi ^ m) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P36

end
