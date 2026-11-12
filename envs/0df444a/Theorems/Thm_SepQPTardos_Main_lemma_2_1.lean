-- Prove2me | Theorems.Thm_SepQPTardos_Main_lemma_2_1
-- name    : SepQPTardos.Main.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:12.739607+00:00
-- url     : https://prove2.me/theorems/5f447724-8dd5-450c-910b-c72299098082
-- title:
--   Lemma 2.1 — conformal decomposition into at most dim ker D circuits
-- statement:
--   Let $D$ be a real $p\times n$ matrix and $v\ne0$ a kernel vector, $Dv=0$. Then there are $k\le\dim\ker D$, coefficients $\lambda_1,\dots,\lambda_k>0$ and circuits $h^1,\dots,h^k$ of $D$, each conformal to $v$, such that
--
--   $$v=\sum_{i=1}^k\lambda_ih^i,$$
--
--   with no coordinate cancellation: $\sum_i|\lambda_ih^i_e|=|v_e|$ for every coordinate $e$. If $D$ is an integer matrix, the circuits can be taken to be primitive integer vectors.
--
--   This is the conformal decomposition of a subspace into elementary vectors [Roc69, Theorem 1], with the bound on the number of terms; it is applied to displacements between optima in Lemmas 3.2, 4.1 and 4.2.
--
--   Differences from the source:
--   - encoding: a matrix D → a real p × n matrix D (integer D as its real cast); reason: the natural generality of the statement; the integer clause is stated for real casts of integer matrices
--   - encoding: the sum has no coordinate cancellation → Σᵢ |λᵢ hⁱ_e| = |v_e| for every e; reason: this is what absence of cancellation means
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §2.1, Lemma 2.1, p. 4 (proof p. 5)

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Circuits

open Matrix

namespace SepQPTardos.Main

/-- Lemma 2.1 (conformal decomposition; Cui–Li–Miao, STOC 2027 #829, p. 4): every nonzero
kernel vector `v` of a real matrix `D` is `v = ∑ᵢ λᵢ hⁱ` with `k ≤ dim ker D` terms, `λᵢ > 0`,
each `hⁱ` a circuit of `D` conformal to `v`, and no coordinate cancellation
(`∑ᵢ |λᵢ hⁱₑ| = |vₑ|`). If `D` is an integer matrix, the circuits can be taken primitive
integer vectors. -/
theorem lemma_2_1 {p n : ℕ} (D : Matrix (Fin p) (Fin n) ℝ) (v : Fin n → ℝ) (hv : v ≠ 0)
    (hDv : D *ᵥ v = 0) :
    (∃ (k : ℕ) (lam : Fin k → ℝ) (h : Fin k → Fin n → ℝ),
      k ≤ Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin D)) ∧
      (∀ i, 0 < lam i ∧ IsCircuit D (h i) ∧ Conformal (h i) v) ∧
      v = ∑ i, lam i • h i ∧ ∀ e, ∑ i, |lam i * h i e| = |v e|) ∧
    (∀ D' : Matrix (Fin p) (Fin n) ℤ, D = castMat D' →
      ∃ (k : ℕ) (lam : Fin k → ℝ) (h : Fin k → Fin n → ℤ),
        k ≤ Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin D)) ∧
        (∀ i, 0 < lam i ∧ Primitive (h i) ∧ IsCircuit D (castIntVec (h i)) ∧
          Conformal (castIntVec (h i)) v) ∧
        v = ∑ i, lam i • castIntVec (h i) ∧
        ∀ e, ∑ i, |lam i * (h i e : ℝ)| = |v e|) := by sorry

end SepQPTardos.Main
