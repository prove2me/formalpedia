-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma1_polarization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma1_polarization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:44:56.36852+00:00
-- url     : https://prove2.me/theorems/0ebb5d23-f09c-4d9c-bec8-044e177677b5
-- title:
--   Lemma 1 (Polarization identity)
-- statement:
--   Let $n,k\ge1$, let $O$ be a Hermitian observable whose Pauli expansion has weight exactly $k$, and let $\rho_{s,i}$ be normalized single-qubit density matrices for $s\in[k]$, $i\in[n]$. Let $\operatorname{pol}(O)$ be the linear polarization obtained by averaging the $k!$ assignments of each Pauli support to the $k$ replica layers. For every $t\in\mathbb R$,
--   $$t^k\operatorname{tr}\!\left(\operatorname{pol}(O)\bigotimes_{s,i}\rho_{s,i}\right)=\frac{k^k}{k!}\mathbb E_{\sigma\in\{\pm1\}^k}\left[\left(\prod_s\sigma_s\right)\operatorname{tr}\!\left(O\bigotimes_i\left[\frac I2+\frac tk\sum_s\sigma_s(\rho_{s,i}-I/2)\right]\right)\right].$$
--   The signs are independent and uniform. This is an algebraic identity for unrestricted real $t$; the inner operator need not be positive when $|t|>1$.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 24, Lemma 1 (Polarization identity)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 1, paper p.24, A35. t is unrestricted; the input factors are
normalized densities. No positivity of productPath at |t|>1 is required. -/
theorem lemma1_polarization (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (O : (Matrix (Qubits n) (Qubits n) ℂ)) (hO : O.IsHermitian) (hhom : IsHomogeneous k O)
    (rho : Fin k → Fin n → Matrix Bool Bool ℂ)
    (hrho : ∀ s i, IsDensityMatrix (rho s i)) (t : ℝ) :
    t ^ k * effectProb (polarization k O) (namedWireTensor (fun si : Fin k × Fin n => rho si.1 si.2)) =
      (k : ℝ) ^ k / (Nat.factorial k : ℝ) * signAverage k (fun sigma =>
        (∏ s, rademacherValue (sigma s)) * effectProb O (productPath t rho sigma)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
