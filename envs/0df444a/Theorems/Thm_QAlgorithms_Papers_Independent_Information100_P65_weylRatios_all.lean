-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P65_weylRatios_all
-- name    : QAlgorithms.Papers.Independent.Information100.P65.weylRatios_all
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:49:33.194396+00:00
-- url     : https://prove2.me/theorems/5f0fd640-5264-4c8d-931a-255ee3c2338a
-- title:
--   Lemma 3.5: Weyl ratios and all three consequences
-- statement:
--   Let $\lambda^+$ and $\lambda$ be Young diagrams with at most $d\ge1$ rows, differing by removal of the box $(j,m)$ from $\lambda^+$, where $1\le j\le d$ and $m=\lambda_j^+\ge1$. Set $\omega_a=\lambda_a-a$ and $\kappa_n=D_n(\lambda^+)/D_n(\lambda)$, where $D_n$ is the dimension of the representation of $U(n)$ with highest weight given by the first $n$ rows. For $j\le n\le d$,
--
--   $$\kappa_n=\prod_{a<j}\frac{\omega_a-\omega_j-1}{\omega_a-\omega_j}\prod_{j<b\le n}\frac{\omega_j-\omega_b+1}{\omega_j-\omega_b},\qquad \frac{\kappa_n}{\kappa_d}=\prod_{n<b\le d}\frac{\omega_j-\omega_b}{\omega_j-\omega_b+1}.$$
--
--   The ratio $\kappa_n/\kappa_d$ depends only on $\lambda_j,\ldots,\lambda_d$. Deleting an existing column of height at least $n$ leaves $\kappa_n$ unchanged. If $\lambda_b=0$ for every $b>n$, then
--
--   $$\frac{\kappa_n}{\kappa_d}=\frac{m+n-j}{m+d-j};$$
--
--   if some $\lambda_b>0$ for $b>n$, the left side is strictly smaller. Empty products equal one. These formulas describe how dimension ratios behave under the diagram reductions used in the channel bounds.
--
--   **Formalization Note** Dimensions are computed by Weyl's product formula. All quotients and differences in that formula are real. Deleting a column is computed directly from the rows; its existence is expressed by the strict drop after its height. Lean row $j$ denotes source row $j+1$.
-- source:
--   Minimal output entropy for the channels that add or remove a box of a Young diagram, and a Pauli principle for every permutation symmetry, arXiv:2609.33498v1, PDF p. 14, Lemma 3.5: Weyl ratios and all three consequences

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P65

attribute [local instance] Classical.propDecidable

/-- Lemma 3.5, Weyl ratios and all consequences (arxiv-2609.33498v1,
PDF p.14, equation (24) and (a)-(c)). Here source j is Lean j+1 and
m=upper.rowLen j. Column deletion uses an actual column height; the object
after deletion is computed, not supplied as an unrelated diagram. -/
theorem weylRatios_all {d j n : ℕ} (lower upper : YoungDiagram)
    (hpair : IsBoxPair d lower upper j) (hjn : j + 1 ≤ n) (hnd : n ≤ d) :
    (dimensionRatio lower.rowLen j n =
      (∏ a ∈ Finset.range j,
        (shiftedRow lower.rowLen a - shiftedRow lower.rowLen j - 1) /
          (shiftedRow lower.rowLen a - shiftedRow lower.rowLen j)) *
      (∏ b ∈ Finset.Ico (j + 1) n,
        (shiftedRow lower.rowLen j - shiftedRow lower.rowLen b + 1) /
          (shiftedRow lower.rowLen j - shiftedRow lower.rowLen b))) ∧
    (dimensionRatio lower.rowLen j n / dimensionRatio lower.rowLen j d =
      ∏ b ∈ Finset.Ico n d,
        (shiftedRow lower.rowLen j - shiftedRow lower.rowLen b) /
          (shiftedRow lower.rowLen j - shiftedRow lower.rowLen b + 1)) ∧
    (∀ other otherUpper : YoungDiagram, IsBoxPair d other otherUpper j →
      (∀ a ∈ Finset.Ico j d, other.rowLen a = lower.rowLen a) →
      dimensionRatio other.rowLen j n / dimensionRatio other.rowLen j d =
        dimensionRatio lower.rowLen j n / dimensionRatio lower.rowLen j d) ∧
    (∀ h : ℕ, n ≤ h → h ≤ d → lower.rowLen h < lower.rowLen (h - 1) →
      dimensionRatio (deletedColumnRows lower.rowLen h) j n =
        dimensionRatio lower.rowLen j n) ∧
    ((∀ b ∈ Finset.Ico n d, lower.rowLen b = 0) →
      dimensionRatio lower.rowLen j n / dimensionRatio lower.rowLen j d =
        ((upper.rowLen j : ℝ) + (n : ℝ) - ((j + 1 : ℕ) : ℝ)) /
          ((upper.rowLen j : ℝ) + (d : ℝ) - ((j + 1 : ℕ) : ℝ))) ∧
    ((∃ b ∈ Finset.Ico n d, 0 < lower.rowLen b) →
      dimensionRatio lower.rowLen j n / dimensionRatio lower.rowLen j d <
        ((upper.rowLen j : ℝ) + (n : ℝ) - ((j + 1 : ℕ) : ℝ)) /
          ((upper.rowLen j : ℝ) + (d : ℝ) - ((j + 1 : ℕ) : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P65

end
