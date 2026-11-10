-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_lemma_A_2
-- name    : RandTensorIso.Smoothed.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:39:11.577209+00:00
-- url     : https://prove2.me/theorems/15fd68d6-dab4-49bb-b176-14c9ed008b0b
-- title:
--   Lemma A.2 — rounding a near-unitary Gaussian-rational matrix to an exactly unitary one, in polynomial time
-- statement:
--   Let $0<\varepsilon_0\le1/(4(2n+1))$ and let $X\in\mathbb Q(i)^{n\times n}$ satisfy $\|X-U\|\le\varepsilon_0$ (operator norm) for a unitary matrix $U$. Then a unitary matrix $\hat X\in\mathbb Q(i)^{n\times n}$ with
--   $$\|\hat X-X\|_F\le9\sqrt n\,(2n+1)^2\varepsilon_0$$
--   can be computed from $X$ in time polynomial in $n$ and the bit length of $X$.
--
--   In Lean: one program and a constant $C$ such that, for every $n$ and $X$, whenever $\varepsilon_0$ and $U$ satisfy the hypotheses, the program on input $(n,X)$ halts within $C(n+|X|)^C+C$ steps with output (the encoding of) such an $\hat X$. Neither $\varepsilon_0$ nor $U$ is an input. Algorithm 3 uses this lemma to make its witness exactly unitary.
--
--   Differences from the source:
--   - encoding: can be computed from X in time polynomial in n and the bit length of X → ∃ a FinTM2 program P and C: on input (n, X) it halts within C(n + |enc X|)^C + C steps and outputs enc X̂ with X̂ unitary and the bound, whenever ε₀ and U satisfy the hypotheses; reason: the paper names no machine; ε₀ and U are not inputs of the procedure, as in its proof
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 61 (PDF 63), Lemma A.2

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor
import Definitions.Def_RandTensorIso_Smoothed_Spectral
import Definitions.Def_RandTensorIso_Smoothed_Machine

open Matrix

namespace RandTensorIso.Smoothed

/-- Lemma A.2 (p. 61). One program, given `n` and `X ∈ ℚ(i)^{n×n}`, halts within a polynomial in
`n` and the bit length of `X` and outputs a matrix `X̂ ∈ ℚ(i)^{n×n}` such that, whenever
`0 < ε₀ ≤ 1/(4(2n+1))` and `‖X − U‖ ≤ ε₀` (operator norm) for a unitary `U`, `X̂` is unitary and
`‖X̂ − X‖_F ≤ 9√n (2n+1)² ε₀`. -/
theorem lemma_A_2 :
    ∃ (P : Program) (C : ℕ), ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) GQ) (ε₀ : ℝ) (V : U n),
      0 < ε₀ → ε₀ ≤ 1 / (4 * (2 * n + 1)) →
      opNorm (gqMat X - (V : Matrix (Fin n) (Fin n) ℂ)) ≤ ε₀ →
      ∃ (Xh : Matrix (Fin n) (Fin n) GQ) (T : ℕ),
        P.HaltsWith (encNat n ++ encGMat X) (encGMat Xh) T ∧
        T ≤ C * (n + (encGMat X).length) ^ C + C ∧
        gqMat Xh ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
        Real.sqrt (∑ i, ∑ j, ‖gqMat Xh i j - gqMat X i j‖ ^ 2) ≤
          9 * Real.sqrt n * (2 * n + 1) ^ 2 * ε₀ := by sorry

end RandTensorIso.Smoothed
