-- Prove2me | Theorems.Thm_SparseWalsh_Approx_lemma_3_1
-- name    : SparseWalsh.Approx.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:02:19.758639+00:00
-- url     : https://prove2.me/theorems/02f6ff62-aed4-428d-9ae1-5e7b790751c6
-- title:
--   Lemma 3.1 — Fourier hashing: a bucket value sums the Fourier coefficients hashed to it
-- statement:
--   Let $m,d\ge0$, $B\in\mathbb F_2^{m\times d}$, $y\in\mathbb F_2^d$ and $f:\mathbb F_2^d\to\mathbb R$. The bucket table of Eq. (3), $H^f_{B,y}(v)=2^{-m}\sum_{z\in\mathbb F_2^m}f(y+B^\top z)(-1)^{\langle v,z\rangle}$, satisfies, for every bucket $v\in\mathbb F_2^m$,
--   $$H^f_{B,y}(v)=\sum_{a:\,Ba=v}\hat f(a)\chi_a(y).$$
--   Each bucket value thus sums the Fourier coefficients that the matrix $B$ assigns to that bucket, each multiplied by the phase $\chi_a(y)$. Every algorithm of the paper builds its bucket tables from this identity, and no rank assumption on $B$ is needed ($m=0$ included).
--
--   Differences from the source:
--
--   - encoding: F_2^d, B ∈ F_2^{m×d} → Fin d → ZMod 2, Matrix (Fin m) (Fin d) (ZMod 2); Bᵀz as the transpose matrix–vector product; reason: same objects
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 13 (PDF p. 16), Lemma 3.1; proof p. 28, App. A.4

import Mathlib
import Definitions.Def_SparseWalsh_Approx_Fourier

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-- **Lemma 3.1** (Fourier hashing), p. 13 (PDF p. 16). For every `B ∈ F_2^{m×d}`, `y ∈ F_2^d`
and `v ∈ F_2^m`, the bucket value of Eq. (3), `H^f_{B,y}(v) = 2^{−m} Σ_z f(y + Bᵀz)(−1)^{⟨v,z⟩}`,
equals `Σ_{a : Ba = v} f̂(a) χ_a(y)`. Every `m ≥ 0` (including `m = 0`) and every real `f`. -/
theorem lemma_3_1 {d m : ℕ} (f : Cube d → ℝ) (B : Matrix (Fin m) (Fin d) (ZMod 2)) (y : Cube d)
    (v : Cube m) :
    bucket f B y v =
      ∑ a ∈ Finset.univ.filter (fun a : Cube d => B *ᵥ a = v), hat f a * chi a y := by sorry

end SparseWalsh.Approx
