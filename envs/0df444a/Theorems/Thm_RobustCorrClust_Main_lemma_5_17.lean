-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_5_17
-- name    : RobustCorrClust.Main.lemma_5_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:41:54.972607+00:00
-- url     : https://prove2.me/theorems/82bddc85-0194-48a0-a74b-3d0fefd60f67
-- title:
--   Lemma 5.17 — diagonal repair of a ν²/2-optimal dual point: Y ∈ Eₙ and f(Y) − p⋆ ≤ 8nR²ν² + 4nRν ≤ 12nR²ν
-- statement:
--   Let $C$ be a weighted adjacency matrix, $R=n+\max_u\sum_vC_{uv}$, $\nu\in(0,1]$ and $a=1+\nu$. Let $y\in B$ be $\nu^2/2$-optimal, $\varphi(y)-\min_{\mathbb R^n}\varphi\le\nu^2/2$, and $X=M(y)^+$. Then $Y:=X/a+\mathrm{Diag}(\mathbf 1-\mathrm{diag}(X)/a)$ satisfies $Y\in E_n$, $Y_{uv}=X_{uv}/a$ for all $u\ne v$, and
--   $$f(Y)-p^\star\le8nR^2\nu^2+4nR\nu\le12nR^2\nu,$$
--   where $f(Z)=\tfrac12\|Z-C\|_F^2$ and $p^\star=\min_{Z\in E_n}f(Z)$.
--
--   Differences from the source:
--   - generalization: $C$ the weighted adjacency matrix of the rescaled sparsifier $\tilde H$ ("here and throughout Part B", p. 21) → $C$ any weighted adjacency matrix (symmetric, nonnegative, zero diagonal), the input class of Theorem 3; reason: Theorem 3 is stated for this general $C$ (p. 21) and the lemma is part of its proof; the paper's $\tilde H$ is such a matrix.
--   - encoding: $\varphi(y)-\min\varphi\le\nu^2/2$ → $\varphi(y)-\varphi(z)\le\nu^2/2$ for every $z$; reason: equivalent.
--   - encoding: $f(Y)-p^\star\le b$ → $f(Y)-f(Z)\le b$ for every $Z\in E_n$; reason: equivalent, $p^\star$ is the minimum of $f$ over $E_n$.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 35, Lemma 5.17

import Mathlib
import Definitions.Def_UniversalSubmod_CorrMatrix
import Definitions.Def_RobustCorrClust_Main_NCMDual

namespace RobustCorrClust.Main

/-- Lemma 5.17 (p. 35): let `ν ∈ (0, 1]`, `a = 1 + ν`, `y ∈ B` with
`φ(y) − min φ ≤ ν²/2`, and `X = M(y)⁺`. Then `Y := X/a + Diag(1 − diag(X)/a)` satisfies
`Y ∈ Eₙ`, `Y_uv = X_uv/a` for `u ≠ v`, and `f(Y) − p⋆ ≤ 8nR²ν² + 4nRν ≤ 12nR²ν`
(`p⋆ = min_{Z ∈ Eₙ} f(Z)`, i.e. `f(Y) − f(Z) ≤ 8nR²ν² + 4nRν` for every `Z ∈ Eₙ`). -/
theorem lemma_5_17 {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsWeightedGraph C)
    (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (y : Fin n → ℝ) (hyB : InBox C y)
    (hopt : ∀ z : Fin n → ℝ, phi C y - phi C z ≤ ν ^ 2 / 2) :
    UniversalSubmod.CorrMatrix (repairY (posPart (Mmat C y)) (1 + ν)) ∧
    (∀ u v, u ≠ v →
        repairY (posPart (Mmat C y)) (1 + ν) u v = posPart (Mmat C y) u v / (1 + ν)) ∧
    (∀ Z : Matrix (Fin n) (Fin n) ℝ, UniversalSubmod.CorrMatrix Z →
        fObj C (repairY (posPart (Mmat C y)) (1 + ν)) - fObj C Z ≤
          8 * n * boxR C ^ 2 * ν ^ 2 + 4 * n * boxR C * ν) ∧
    8 * n * boxR C ^ 2 * ν ^ 2 + 4 * n * boxR C * ν ≤ 12 * n * boxR C ^ 2 * ν := by sorry

end RobustCorrClust.Main
