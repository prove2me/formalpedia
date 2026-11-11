-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_5_16
-- name    : RobustCorrClust.Main.lemma_5_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:41:44.60552+00:00
-- url     : https://prove2.me/theorems/40c930d2-b990-41cd-890b-761a0bec9dd9
-- title:
--   Lemma 5.16 — with ν³-accurate gradients, Algorithm 1 yields Y ∈ Eₙ with ½‖Y − C‖²_F ≤ min_{Eₙ} ½‖Z − C‖²_F + ξ
-- statement:
--   Let $C$ be a weighted adjacency matrix, $\xi\in(0,1]$, and $\nu=\xi/(100nR^2)$, $a=1+\nu$ the parameters of Algorithm 1. Suppose that at every iteration $t\le T$ and for every vertex $u$, the vector $x^{t,u}$ obtained by line 4 satisfies $|x^{t,u}_u-(M(y_t)^+)_{uu}|\le\nu^3$. Then the output $\bar y$ lies in $B$, and with $X=M(\bar y)^+$ the matrix $Y=X/a+\mathrm{Diag}(\mathbf 1-\mathrm{diag}(X)/a)$ of the conceptual process satisfies $Y\in E_n$, $Y_{uv}=X_{uv}/a$ for all $u\ne v$, and
--   $$\tfrac12\|Y-C\|_F^2\le\min_{Z\in E_n}\tfrac12\|Z-C\|_F^2+\xi .$$
--
--   Differences from the source:
--   - generalization: the vector computed by Polynomial-Approx in line 4 → any vectors $x^{t,u}$ meeting the accuracy hypothesis at the current iterate; reason: as in Lemma 5.15, Algorithm 3's output is such a family.
--   - encoding: $\le\min_{Z\in E_n}\tfrac12\|Z-C\|_F^2+\xi$ → $\le\tfrac12\|Z-C\|_F^2+\xi$ for every $Z\in E_n$; reason: equivalent, the minimum is attained ($E_n$ is compact).
--   - encoding: $n=0$ → included without hypothesis; reason: $\nu$ is undefined at $n=0$ in the paper; the Lean statement is trivially true there.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 35, Lemma 5.16

import Mathlib
import Definitions.Def_UniversalSubmod_CorrMatrix
import Definitions.Def_RobustCorrClust_Main_NCMDual

namespace RobustCorrClust.Main

/-- Lemma 5.16 (p. 35): if at every iteration of Algorithm 1 and for every vertex `u` the vector
`x` obtained by line 4 satisfies `|x_u − (M(y_t)⁺)_uu| ≤ ν³`, `ν = ξ/(100nR²)`, then the output
`ȳ` lies in `B`, and the matrix `Y = X/a + Diag(1 − diag(X)/a)`, `X = M(ȳ)⁺`, of the conceptual
process satisfies `Y ∈ Eₙ`, `Y_uv = X_uv/a` for `u ≠ v`, and
`½‖Y − C‖²_F ≤ min_{Z ∈ Eₙ} ½‖Z − C‖²_F + ξ`. The oracle `x` is arbitrary subject to this
accuracy. -/
theorem lemma_5_16 {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsWeightedGraph C)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1) (x : ℕ → Fin n → Fin n → ℝ)
    (hx : ∀ t, 1 ≤ t → t ≤ iterPar C ξ → ∀ u,
      |x t u u - posPart (Mmat C (pgdY C ξ x t)) u u| ≤ nuPar C ξ ^ 3) :
    InBox C (pgdOut C ξ x) ∧
    UniversalSubmod.CorrMatrix (repairY (posPart (Mmat C (pgdOut C ξ x))) (aPar C ξ)) ∧
    (∀ u v, u ≠ v →
        repairY (posPart (Mmat C (pgdOut C ξ x))) (aPar C ξ) u v =
          posPart (Mmat C (pgdOut C ξ x)) u v / aPar C ξ) ∧
    (∀ Z : Matrix (Fin n) (Fin n) ℝ, UniversalSubmod.CorrMatrix Z →
        fObj C (repairY (posPart (Mmat C (pgdOut C ξ x))) (aPar C ξ)) ≤ fObj C Z + ξ) := by sorry

end RobustCorrClust.Main
