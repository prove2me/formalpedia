-- Prove2me | Theorems.Thm_SchattenSketch_Main_lemma_4_6
-- name    : SchattenSketch.Main.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:57:33.558387+00:00
-- url     : https://prove2.me/theorems/04efdd01-18e4-4437-853a-eb0f6e79d84b
-- title:
--   Lemma 4.6 — odd two-sided rotation bound: $E\|P^{\otimes m}(U\otimes V)^{\otimes m}T\|^2\le(C m)^{Cm}(k/n^2)^{(m+1)/2}\|T\|^2$
-- statement:
--   Let $H=\mathbb R^{n\times n}$ and equip $H^{\otimes m}$ with the Frobenius norm. There is an absolute constant $C_{ten}\ge 1$ such that: if $m$ is odd and $(4m)^{4m}\le n/2$, then for every tensor $T\in H^{\otimes m}$ and every rank-$k$ orthogonal projection $P$ on $H$,
--   $$\mathbb E_{U,V}\,\bigl\|P^{\otimes m}(U\otimes V)^{\otimes m}T\bigr\|^2\le(C_{ten}m)^{C_{ten}m}\Bigl(\frac k{n^2}\Bigr)^{(m+1)/2}\|T\|^2,$$
--   where $U,V$ are independent Haar-distributed elements of $O_n$.
--
--   This is the measurement-contraction estimate: after random rotations on both sides, a rank-$k$ measurement sees only a $(k/n^2)^{(m+1)/2}$ fraction of an odd-order tensor's energy. Lemma 4.7 applies it at $m=2K+1$.
--
--   **Formalization Note.** Tensors are `MatTensor n m`; $(U\otimes V)^{\otimes m}$ and $P^{\otimes m}$ are `rotTensor` and `projTensor` in index form. A rank-$k$ orthogonal projection is an $n^2\times n^2$ matrix with $P^\top=P$, $P^2=P$, $\mathrm{rank}\,P=k$. The expectation is the Bochner integral over `haarO n ⊗ haarO n`; the integrand is a polynomial in the entries of $U,V$, hence integrable on the compact group.
--
--   Differences from the source:
--   - encoding: H^{⊗m} with the Frobenius norm; (U ⊗ V)^{⊗m}; P^{⊗m} → arrays (Fin m → Fin n × Fin n) → ℝ with Σ squares; rotTensor, projTensor in index form; reason: coordinates of the same tensors and operators
--   - encoding: rank-k orthogonal projection P on H → P : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ with Pᵀ = P, P * P = P, P.rank = k; reason: the same operators
--   - encoding: E_{U,V} with U, V independent Haar → Bochner integral over (haarO n).prod (haarO n); reason: the integrand is continuous on a compact group, so integrable
--   - encoding: (4m)^{4m} ≤ n/2; (C m)^{Cm}, (k/n²)^{(m+1)/2} → real inequality; real powers (rpow); reason: same values; (m + 1)/2 is an integer for odd m
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 19, Lemma 4.6, (4.22) (proof pp. 19–21 and App. B)

import Mathlib
import Definitions.Def_FourierRankQLB_Od
import Definitions.Def_FourierRankQLB_haarO
import Definitions.Def_SchattenSketch_Main_Tensor

open MeasureTheory FourierRankQLB

namespace SchattenSketch.Main

/-- Lemma 4.6 (odd two-sided rotation bound; Yang, p. 19). There is an absolute constant
`C_ten ≥ 1` such that for odd `m` with `(4m)^{4m} ≤ n/2`, every tensor `T ∈ H^{⊗m}`,
`H = ℝ^{n×n}`, and every rank-`k` orthogonal projection `P` on `H`,
`E_{U,V} ‖P^{⊗m} (U ⊗ V)^{⊗m} T‖² ≤ (C_ten m)^{C_ten m} (k/n²)^{(m+1)/2} ‖T‖²`,
with `U, V` independent Haar-distributed on `O_n`. -/
theorem lemma_4_6 :
    ∃ C_ten : ℝ, 1 ≤ C_ten ∧
      ∀ (n m k : ℕ), Odd m → ((4 * m : ℕ) : ℝ) ^ (4 * m) ≤ (n : ℝ) / 2 →
      ∀ (T : MatTensor n m) (P : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ),
        P.transpose = P → P * P = P → P.rank = k →
        ∫ UV : Od n × Od n,
            tensorNormSq (projTensor P
              (rotTensor (UV.1 : Matrix (Fin n) (Fin n) ℝ) (UV.2 : Matrix (Fin n) (Fin n) ℝ) T))
          ∂((haarO n).prod (haarO n)) ≤
        (C_ten * m) ^ (C_ten * m) * ((k : ℝ) / (n : ℝ) ^ 2) ^ (((m : ℝ) + 1) / 2) *
          tensorNormSq T := by sorry

end SchattenSketch.Main
