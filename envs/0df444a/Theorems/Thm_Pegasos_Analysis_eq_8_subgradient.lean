-- Prove2me | Theorems.Thm_Pegasos_Analysis_eq_8_subgradient
-- name    : Pegasos.Analysis.eq_8_subgradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:03.796116+00:00
-- url     : https://prove2.me/theorems/8aa55c06-94dd-40f0-af97-cf7f30ed2892
-- title:
--   Eq. (8) is a sub-gradient of the mini-batch objective f(·; A)
-- statement:
--   Let $\lambda > 0$, let $(x_i,y_i)_{i\in[m]}$ be examples with $x_i\in\mathbb R^n$, $y_i\in\mathbb R$, and let $A$ be a mini-batch of $k$ indices. For every $w$, the vector
--   $$\nabla = \lambda w - \frac1k\sum_{i\in A}\mathbb 1\bigl[y_i\langle w, x_i\rangle < 1\bigr]\, y_i x_i$$
--   of Eq. (8) is a sub-gradient at $w$ of the instantaneous objective $f(w;A) = \frac\lambda2\|w\|^2 + \frac1k\sum_{i\in A}\max\{0, 1 - y_i\langle w, x_i\rangle\}$ of Eq. (7): $f(u;A) - f(w;A) \ge \langle\nabla, u - w\rangle$ for all $u$.
--
--   This is what makes each Pegasos step a sub-gradient step on $f(\cdot;A_t)$, so that Lemma 1 applies.
--
--   **Formalization Note.** The statement holds for every real label (at the kink $y_i\langle w,x_i\rangle = 1$ the chosen value $0$ is a sub-gradient of the hinge), so no $\pm1$ hypothesis is needed. The mini-batch is a $k$-tuple of indices; repeated indices are allowed.
-- source:
--   Shalev-Shwartz, Singer, Srebro & Cotter, Pegasos: primal estimated sub-gradient solver for SVM, Math. Program. 127 (2011), p. 8, §2.3, Eq. (8) (and Eq. (7)); used in the proof of Theorem 1, p. 11

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

namespace Pegasos.Analysis

/-- **Eq. (8)** (p. 8, §2.3): the vector `∇ = λw − (1/k) Σ_{i∈A} 1l[yᵢ⟨w, xᵢ⟩ < 1] yᵢxᵢ` is a
sub-gradient of the instantaneous objective `f(·; A)` of Eq. (7) at `w`, for every
mini-batch `A` and every `w`. -/
theorem eq_8_subgradient {n m k : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (B : Fin k → Fin m)
    (w : EuclideanSpace ℝ (Fin n)) :
    UnderstandingML.IsSubgradient (instObj lam x y B) w (subgrad lam x y B w) := by sorry

end Pegasos.Analysis
