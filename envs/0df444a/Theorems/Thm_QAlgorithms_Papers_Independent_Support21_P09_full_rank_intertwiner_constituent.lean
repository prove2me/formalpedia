-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_full_rank_intertwiner_constituent
-- name    : QAlgorithms.Papers.Independent.Support21.P09.full_rank_intertwiner_constituent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:45:22.08499+00:00
-- url     : https://prove2.me/theorems/df224abb-b465-4b23-a339-a18d9c6c4474
-- title:
--   A full-row-rank intertwiner implies an actual constituent
-- statement:
--   Let $G$ be a finite group and let $\psi_1:G\to\mathrm{GL}_d(\mathbb C)$ and $\psi_2:G\to\mathrm{GL}_n(\mathbb C)$ be ordinary representations of positive degree. If $M\in\mathbb C^{d\times n}$ has rank $d$ and $\psi_1(g)M=M\psi_2(g)$ for every $g$, then $d\le n$. Moreover, there exist $c\ge0$ with $n=d+c$, a representation $\chi:G\to\mathrm{GL}_c(\mathbb C)$ and mutually inverse coordinate maps $S:\mathbb C^d\oplus\mathbb C^c\to\mathbb C^n$ and $T$ such that
--
--   $$
--   T\psi_2(g)S=\psi_1(g)\oplus\chi(g),\qquad ST=I_n,\quad TS=I_{d+c}.
--   $$
--
--   Thus $\psi_1$ is an actual direct summand, rather than just a quotient or a shared irreducible constituent. In finite dimensions the Lean hypothesis uses surjectivity of the matrix map, which is equivalent to full row rank; unitarity is not assumed.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 10, Theorem 5: full-row-rank intertwiner implies constituent

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF p.10, Theorem 5: a full-row-rank intertwiner yields an actual direct summand.
Surjectivity of the matrix map is exactly rank(M)=d in these finite-dimensional spaces.
The base changes are invertible, not necessarily unitary; the proof's "unitary" is an
unnecessary restriction that is not part of the printed theorem's hypotheses. -/
theorem full_rank_intertwiner_constituent
    {G : Type*} [Group G] [Fintype G] {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (psi1 : Rep G (Fin d)) (psi2 : Rep G (Fin n))
    (M : Matrix (Fin d) (Fin n) ℂ) (hM : MatrixIntertwines psi1 psi2 M)
    (hrank : Function.Surjective M.mulVec) :
    d ≤ n ∧ ∃ c : ℕ, n = d + c ∧ ∃ chi : Rep G (Fin c),
    ∃ S : Matrix (Fin n) (Fin d ⊕ Fin c) ℂ,
    ∃ T : Matrix (Fin d ⊕ Fin c) (Fin n) ℂ,
      S * T = 1 ∧ T * S = 1 ∧
      ∀ g, T * psi2 g * S = Matrix.fromBlocks (psi1 g) 0 0 (chi g) := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end
