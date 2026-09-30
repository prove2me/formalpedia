-- Prove2me | Theorems.Thm_UnderstandingML_johnson_lindenstrauss
-- name    : UnderstandingML.johnson_lindenstrauss
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:24:14.29229+00:00
-- url     : https://prove2.me/theorems/7eeca72c-e136-486c-832a-ef989a926318
-- title:
--   Lemma 23.4 (Johnson–Lindenstrauss): for finite Q and ε = √(6 log(2|Q|/δ)/n) ≤ 3/4, a random N(0,1/n) matrix has sup_{x∈Q} |‖Wx‖²/‖x‖² − 1| < ε with probability ≥ 1 − δ
-- statement:
--   **Lemma 23.4 (Johnson-Lindenstrauss Lemma).** Let $Q$ be a finite set of vectors in $\mathbb{R}^d$. Let $\delta \in (0,1)$ and $n$ be an integer such that $\epsilon = \sqrt{6\log(2|Q|/\delta)/n} \le 3/4$. Then, with probability of at least $1 - \delta$ over a choice of a random matrix $W \in \mathbb{R}^{n \times d}$ such that each element of $W$ is distributed normally with zero mean and variance of $1/n$ we have
--   $$\sup_{x \in Q}\Big|\frac{\|Wx\|^2}{\|x\|^2} - 1\Big| < \epsilon.$$
--
--   Formally: the vectors of $Q$ are nonzero, $n \ge 1$, and the failure event $\{\exists x \in Q : |\|Wx\|^2/\|x\|^2 - 1| \ge \epsilon\}$ has probability at most $\delta$.
--
--   **Why $\epsilon \le 3/4$.** The lemma is Lemma 23.3 with a union bound over $Q$. The printed condition $\epsilon \le 3$ inherits Lemma 23.3's false range: with $|Q| = 1$, $\epsilon = 1$ and large $n$, $P[\chi^2_n \ge 2n]$ exceeds $\delta = 2e^{-n/6}$. The proofs that use the lemma (Lemma 23.12) apply it at $\epsilon/2 < 1/2$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §23.2 pp. 329-330, Lemma 23.4 with its proof

import Definitions.Def_UnderstandingML_DimReduction

open MeasureTheory ProbabilityTheory

namespace UnderstandingML

/-- **Lemma 23.4 (Johnson-Lindenstrauss Lemma)** (p. 329). Let `Q` be a finite set of vectors in
`ℝ^d`. Let `δ ∈ (0, 1)` and `n` be an integer such that `ε = √(6 log(2|Q|/δ)/n) ≤ 3/4`. Then, with
probability of at least `1 − δ` over a choice of a random matrix `W ∈ ℝ^{n×d}` such that each
element of `W` is distributed normally with zero mean and variance of `1/n` we have
`sup_{x ∈ Q} |‖Wx‖²/‖x‖² − 1| < ε`. The vectors of `Q` are nonzero and `n ≥ 1`. The book's condition `ε ≤ 3` inherits the false range of
Lemma 23.3: for `|Q| = 1` and `ε = 1` it fails for large `n`. -/
theorem johnson_lindenstrauss {d : ℕ} (Q : Finset (Fin d → ℝ)) (hQ : ∀ x ∈ Q, x ≠ 0) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (n : ℕ) (hn : 0 < n)
    (hε : Real.sqrt (6 * Real.log (2 * Q.card / δ) / n) ≤ 3 / 4) :
    gaussianMatrixLaw n d (n : NNReal)⁻¹
      {W | ∃ x ∈ Q, Real.sqrt (6 * Real.log (2 * Q.card / δ) / n) ≤
        |sqNorm ((Matrix.of W).mulVec x) / sqNorm x - 1|} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML
