-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_cat_firstUndetectable
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.cat_firstUndetectable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:29:24.128724+00:00
-- url     : https://prove2.me/theorems/b1297f7b-30c8-4c5a-a109-9629e7c07f8b
-- title:
--   First undetectable cat loss and bit-flip saturation
-- statement:
--   Fix $S\ge0$ and $0<\gamma<1$. In the normalized cat basis with real amplitude $a>0$, write $N_a^r$ for projected-coherent normalization probabilities and $\epsilon_{\ell k}$ for the compression of $E_\ell^\dagger E_k$. Then
--
--   $$\epsilon_{0,S+1}=\frac{(\sqrt\gamma a)^{S+1}e^{-\gamma a^2}}{\sqrt{(S+1)!N_a^0N_a^{S+1}}}\begin{pmatrix}0&N_{a\sqrt{1-\gamma}}^0\\N_{a\sqrt{1-\gamma}}^{S+1}&0\end{pmatrix}.$$
--
--   Let $c_{\ell k}$ be the identity coefficient and $x_{\ell k}$ the logical-X coefficient of the actual block. Both $c_{00}$ and $c_{S+1,S+1}$ are positive at every finite $a>0$, and
--
--   $$\frac{x_{0,S+1}}{\sqrt{c_{00}c_{S+1,S+1}}}\longrightarrow1\qquad(a\to\infty).$$
--
--   This ratio statement preserves the source's meaning of asymptotic saturation even when all entries tend to zero.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 11, §V B (5.15)–(5.16): first undetectable cat loss and its saturation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.11 (5.15)--(5.16): first undetectable loss and ratio saturation of the
bit-flip Cauchy--Schwarz bound; both probabilities may vanish as a grows. -/
theorem cat_firstUndetectable (S : ℕ) (g : ℝ) (hg0 : 0 < g) (hg1 : g < 1) :
    (∀ a > (0 : ℝ), qecBlock (catCodeCoordinates a S) g 0 (S + 1) =
      (((Real.sqrt g * a) ^ (S + 1) * Real.exp (-g * a ^ 2) /
        Real.sqrt ((Nat.factorial (S + 1) : ℝ) * catNorm a S 0 * catNorm a S (S + 1))) : ℂ) •
          !![0, (catNorm (a * Real.sqrt (1 - g)) S 0 : ℂ);
             (catNorm (a * Real.sqrt (1 - g)) S (S + 1) : ℂ), 0]) ∧
    (∀ a > (0 : ℝ), 0 < qecC (catCodeCoordinates a S) g 0 0 ∧ 0 < qecC (catCodeCoordinates a S) g (S + 1) (S + 1)) ∧
    Tendsto (fun a => qecX (catCodeCoordinates a S) g 0 (S + 1) /
      Real.sqrt (qecC (catCodeCoordinates a S) g 0 0 * qecC (catCodeCoordinates a S) g (S + 1) (S + 1))) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
