-- Prove2me | Theorems.Thm_PermDiameter_Binary_lemma_3_2
-- name    : PermDiameter.Binary.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:11:22.066209+00:00
-- url     : https://prove2.me/theorems/cff4bafb-c50b-454c-a26b-0fe9dcc7d428
-- title:
--   Lemma 3.2 — the least $n$ with (3.2), the numbers $q,m,d_c$ of (3.1), and a permutation of order $q^2$ on $d_c$ points, in polynomial time
-- statement:
--   Let $p_1=3,p_2=5,\dots$ be the odd primes. Given an instance $(\Sigma_0,g_0,k_0)$ of Binary Length of degree $d_0$, one can compute in polynomial time the least $n\ge1$ such that
--   $$q=\prod_{j=1}^n p_j^2,\qquad m=\frac{q+3}{4},\qquad d_c=\sum_{j=1}^n p_j^4\qquad\text{satisfy}\qquad m\ge k_0+10(d_0+d_c)^4+3 .$$
--   Moreover, one can compute in polynomial time a permutation $c$ of order $q^2$ on a set $\Omega_c$ of size $d_c$.
--
--   These are the parameters of the reduction of Theorem 3.1: $q$ is the order of the clock, $m$ the output threshold, and $c$ realises $C_{q^2}$ and $C_q=\langle c^q\rangle$.
--
--   **Formalization Note.** The first map returns $(n,q,m,d_c)$ in binary, with $n$ least such that $1\le n$ and `Cond32` holds; the second returns $(d_c, c)$ as a degree and image list. Instances are `LengthInstance`s with $g_0\in\langle\Sigma_0\rangle$, encoded by `encLength` ($k_0$ in binary).
--
--   Differences from the source:
--   - reading: "compute the least n ≥ 1 such that q, m, d_c (3.1) satisfy (3.2)" → the map outputs (n, q, m, d_c); reason: q, m, d_c are determined by n and have polynomially many bits, so outputting them is equivalent to outputting n
--   - encoding: p₁, p₂, … (1-indexed odd primes); m = (q + 3)/4 → oddPrime 0, oddPrime 1, …; natural-number division; reason: same numbers, and the division is exact because q ≡ 1 (mod 4)
--   - encoding: "in polynomial time" → Turing.TM2ComputableInPolyTime on encLength (binary k₀, image lists) and binary/image-list outputs; reason: the paper's input format with an explicit machine model
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 13, Lemma 3.2 with (3.1), (3.2)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Problems
import Definitions.Def_PermDiameter_Binary_Wreath
import Definitions.Def_PermDiameter_Binary_Parameters

open Equiv OptimalQueuingComplexity.Restless

namespace PermDiameter.Binary

/-- **Lemma 3.2.** Given an instance `(Σ₀, g₀, k₀)` of Binary Length, one can compute in
polynomial time the least `n ≥ 1` such that `q = ∏_{j ≤ n} p_j²`, `m = (q + 3)/4` and
`d_c = ∑_{j ≤ n} p_j⁴` (3.1) satisfy `m ≥ k₀ + 10 (d₀ + d_c)⁴ + 3` (3.2) (output together with
`q, m, d_c`), and, in polynomial time, a permutation `c` of order `q²` on a set of size `d_c`. -/
theorem lemma_3_2 :
    ∃ (N : {x : LengthInstance // x.Valid} → ℕ × ℕ × ℕ × ℕ)
      (C : {x : LengthInstance // x.Valid} → PermWithDegree),
      Nonempty (Turing.TM2ComputableInPolyTime (fun x => encLength x.1) encNat4 N) ∧
      Nonempty (Turing.TM2ComputableInPolyTime (fun x => encLength x.1) encPermWithDegree C) ∧
      ∀ x : {x : LengthInstance // x.Valid}, ∃ n : ℕ,
        N x = (n, qOf n, mOf n, dcOf n) ∧ 1 ≤ n ∧ Cond32 x.1.d x.1.k n ∧
        (∀ n' : ℕ, 1 ≤ n' → Cond32 x.1.d x.1.k n' → n ≤ n') ∧
        (C x).1 = dcOf n ∧ orderOf (C x).2 = qOf n ^ 2 := by sorry

end PermDiameter.Binary
