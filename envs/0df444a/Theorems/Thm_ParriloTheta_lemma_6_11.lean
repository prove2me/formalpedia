-- Prove2me | Theorems.Thm_ParriloTheta_lemma_6_11
-- name    : ParriloTheta.lemma_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:00.65044+00:00
-- url     : https://prove2.me/theorems/cf335f83-682f-474d-ab9a-e0f6f879453e
-- title:
--   Lemma 6.11 — positive semidefiniteness of (6.5) (corrected: $a\ge c$ only when $\alpha-k\ge2$)
-- statement:
--   Let $\alpha>k\ge2$ be integers and $b\in\mathbb R$, and let $a,c$ be given by (6.6). The matrix (6.5),
--   $$
--   \begin{pmatrix} M_b & \big(\tfrac{\alpha}{2}-\tfrac{\alpha}{2k}-1\big)\mathbf 1\\ \big(\tfrac{\alpha}{2}-\tfrac{\alpha}{2k}-1\big)\mathbf 1^{T} & \alpha-1\end{pmatrix},\qquad M_b=(a-c)I_{\alpha-k}+cJ_{\alpha-k},
--   $$
--   is positive semidefinite if and only if
--   1. $a\ge c$ whenever $\alpha-k\ge2$, and
--   2. $\alpha\le k+4+\dfrac{4}{k-1}$.
--
--   Condition 2 is what yields the bound (6.2) of Theorem 6.6.
--
--   Differences from the source:
--   - correction: (i) a ≥ c → (i) a ≥ c required only when α − k ≥ 2; reason: for α − k = 1 the block M_b is 1 × 1 and the printed iff is false: k = 2, α = 3, b = −100 give a = 2 < c = 98 while (6.5) = [[2, −1/4], [−1/4, 2]] ⪰ 0; the proof's step (a − c)I + c′J ⪰ 0 ⇔ a ≥ c ∧ … needs α − k ≥ 2
--   - generalization: b the constant of Lemma 6.8 → any b ∈ ℝ; reason: the proof does not use where b comes from, so the constant of Lemma 6.8 is one instance; Lemma 6.12 applies the lemma at b = −1
--   - reading: M_b is indexed by V (Lemma 6.10, p.21) → M_b is indexed by W; reason: M_b is the W-block of (6.5) and is square of size α − k
--   - encoding: blocks indexed by W (|W| = α − k) and {v} → Fin (α − k) ⊕ Unit; reason: Lean convention
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Lemma 6.11, p.22 (with (6.5)–(6.6), p.21; standing assumption α > k ≥ 2 of §6.2.1, p.20)

import Mathlib
import Definitions.Def_ParriloTheta_coeffA
import Definitions.Def_ParriloTheta_coeffC
import Definitions.Def_ParriloTheta_matrix65

namespace ParriloTheta

/-- **Lemma 6.11: when the matrix (6.5) is positive semidefinite (corrected at `α = k + 1`).**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Lemma 6.11, p.22, under the standing assumption of §6.2.1 (Theorem 6.6, p.20:
"Given integers α > k ≥ 2"):
"The matrix in Eq. (6.5) is positive semidefinite if and only if the following two conditions
hold: (i) a ≥ c, (ii) α ≤ k + 4 + 4/(k−1)."

**Correction.** Condition (i) is required only when `α − k ≥ 2`. When `α − k = 1` the block
`M_b` is the `1 × 1` matrix `(a)` and (i) plays no role: for `k = 2`, `α = 3`, `b = −100` one
has `a = 2 < c = 98`, yet (6.5) is `[[2, −1/4], [−1/4, 2]] ⪰ 0`.

**Generalization.** On the page `b` is the constant of Lemma 6.8; here `b` is any real. The proof
does not use where `b` comes from, and Lemma 6.12 already applies the lemma at `b = −1`.

**Formalization Note.** The matrix is `matrix65 α k b` (blocks `W = Fin (α − k)` and `{v}`);
`a = coeffA α k b`, `c = coeffC k b` (6.6). All arithmetic is in `ℝ`. -/
theorem lemma_6_11 (α k : ℕ) (hk : 2 ≤ k) (hαk : k < α) (b : ℝ) :
    (matrix65 α k b).PosSemidef ↔
      ((2 ≤ α - k → coeffC k b ≤ coeffA α k b) ∧
        (α : ℝ) ≤ (k : ℝ) + 4 + 4 / ((k : ℝ) - 1)) := by sorry

end ParriloTheta
