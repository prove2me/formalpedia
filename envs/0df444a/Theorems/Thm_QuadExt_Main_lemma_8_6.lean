-- Prove2me | Theorems.Thm_QuadExt_Main_lemma_8_6
-- name    : QuadExt.Main.lemma_8_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:35.128892+00:00
-- url     : https://prove2.me/theorems/57f29d4d-c310-42cf-ad4f-16b3119e26cb
-- title:
--   Lemma 8.6 — a Sidon-weighted combination $\sum_i b_i(t) t^{w_i} G_i$ has a non-zero $r \times r$ minor, $r \ge \min(\sqrt d, d/(2p))$
-- statement:
--   Let $F$ be a field and $G_1, \dots, G_n \in F^{k \times k}$ with $\dim_F \operatorname{span}\{G_i y\}_{i \in [n]} \ge d$ for every non-zero $y \in F^k$. Let $w_1, \dots, w_n$ be distinct positive integers forming a Sidon set. Then for every vector of polynomials $b(t) \in F[t]^n$ with $|\{i : b_i(0) \ne 0\}| \ge n - p$, the polynomial matrix
--   $$M(t) = \sum_{i=1}^n b_i(t)\, t^{w_i}\, G_i \in F[t]^{k \times k}$$
--   has a non-zero $r \times r$ minor for some $r \ge \min(\sqrt d, d/(2p))$. This is the step of the large-field rank-combiner construction (Theorem 8.5) that turns the dimension hypothesis into a large non-singular submatrix.
--
--   Differences from the source:
--   - reading: "for all non-zero $y \in F$" → for all non-zero $y \in F^k$; reason: obvious typo, $G_i y$ requires $y \in F^k$, as in Definition 8.2 and Lemma 8.8 (INSIGHTS I3).
--   - encoding: $r \ge \min(\sqrt d, d/(2p))$ → $\sqrt d \le r \lor d \le 2pr$; reason: the same for $p \ge 1$; at $p = 0$ it is the $+\infty$ reading of $d/(2p)$, avoiding Lean's $x/0 = 0$.
--   - encoding: a non-zero $r \times r$ minor → row and column selections `Fin r → Fin k` with non-zero determinant of the submatrix; reason: a selection with a repeated row or column has determinant $0$, so this is a genuine minor.
--   - encoding: $|\{i : b_i(0) \ne 0\}| \ge n - p$ → compared in $\mathbb Z$; $d, p$ natural; reason: avoids truncated subtraction.
--   - reading: $G_i \in F^{k \times k}$ → $k \ge 1$; reason: at $k = 0$ the hypothesis on non-zero $y$ is vacuous and a $0 \times 0$ matrix has no $r \times r$ minor with $r \ge 1$, a degenerate case the lemma does not address (its hypothesis is about non-zero vectors $y \in F^k$).
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 27 (PDF 28), Lemma 8.6

import Mathlib
import Definitions.Def_QuadExt_Main_RankCombiner

namespace QuadExt.Main

open Polynomial Classical in
/-- **Lemma 8.6** (p. 27): if `G_1, …, G_n ∈ F^{k×k}` have `dim_F span{G_i y} ≥ d` for every
non-zero `y ∈ F^k`, the positive integers `w_1, …, w_n` form a Sidon set, and `b(t) ∈ F[t]^n` has
`b_i(0) ≠ 0` for at least `n − p` indices, then `M(t) = Σ_i b_i(t) t^{w_i} G_i` has a non-zero
`r × r` minor with `r ≥ min(√d, d/(2p))`. -/
theorem lemma_8_6 {F : Type} [Field F] (n k d : ℕ) (hk : 0 < k)
    (G : Fin n → Matrix (Fin k) (Fin k) F)
    (hG : ∀ y : Fin k → F, y ≠ 0 →
      d ≤ Module.finrank F (Submodule.span F (Set.range fun i => Matrix.mulVec (G i) y)))
    (w : Fin n → ℕ) (hw_inj : Function.Injective w) (hw_pos : ∀ i, 0 < w i)
    (hw_sidon : IsSidon (Finset.univ.image w))
    (p : ℕ) (b : Fin n → F[X])
    (hb : (n : ℤ) - p ≤ ((Finset.univ.filter fun i => (b i).eval 0 ≠ 0).card : ℤ)) :
    ∃ r : ℕ, (Real.sqrt d ≤ r ∨ d ≤ 2 * p * r) ∧
      ∃ rows cols : Fin r → Fin k,
        ((∑ i, (b i * X ^ w i) • (G i).map C).submatrix rows cols).det ≠ 0 := by sorry

end QuadExt.Main
