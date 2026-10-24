-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_example_3_6
-- name    : QAlgorithms.Papers.Independent.Support50.P12.example_3_6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:24:56.757251+00:00
-- url     : https://prove2.me/theorems/f3f67a54-2e73-4a8a-b4bb-7eb7fb8c0d06
-- title:
--   Example (new estimates) 3.6
-- statement:
--   Let $H$ have dimension $d>1$ and fix an orthonormal basis for transpose. For real $\varepsilon$, define $\Phi_\varepsilon(X)=(1-\varepsilon)X^T+\varepsilon(\operatorname{Tr}X)I/d$, $\Psi_\varepsilon(X)=(1-\varepsilon)X+\varepsilon(\operatorname{Tr}X)I/d$, and $\Lambda_\varepsilon(X)=(1-\varepsilon)X^T+\varepsilon X$. The Schwarz norm is the least nonnegative $c$ with $\Phi(X)^*\Phi(X)\le c\Phi(X^*X)$ for all $X$, and is infinite if no such $c$ exists.
--
--   For $0<\varepsilon<1$, $\Phi_\varepsilon$ is Schwarz and
--
--   $$\frac{d(1-\varepsilon)^2}{\varepsilon}\le\|\Phi_\varepsilon\|_S\le\frac{d(1-\varepsilon)^2+2\varepsilon(1-\varepsilon)\sqrt d+\varepsilon^2}{\varepsilon}.$$
--
--   Its defect has the six-term expansion in the source, and for $c\ge0$, $0\le\varepsilon<1$, it is bounded below by $(\operatorname{Tr}X^*X)I[c\varepsilon-d(1-\varepsilon)^2-2\varepsilon(1-\varepsilon)\sqrt d-\varepsilon^2]/d$. Matrix units give the diagonal defect $\|\Phi_\varepsilon\|_S\varepsilon/d-(1-\varepsilon)^2\ge0$. The Schwarz norm tends to infinity as $\varepsilon\downarrow0$, whereas the operator norm is one for $0\le\varepsilon\le1+1/(d-1)$; the norms are strictly different when $(1-\varepsilon)^2/\varepsilon>d$. Some $\Phi_\varepsilon$ are Schwarz contractions without being two-positive. Further, $\Psi_\varepsilon$ is Schwarz exactly for $0\le\varepsilon<1+1/(d-1)$, with Schwarz norm tending to infinity at that upper endpoint. For $i
--   e j$, the $i$-th diagonal defect of $\Lambda_\varepsilon$ at $X=|e_i\rangle\langle e_j|$ equals $-(1-\varepsilon)^2$ for every real $c$, so $\Lambda_\varepsilon$ is Schwarz exactly when $\varepsilon=1$. These are the authors' new estimates and conclusions; classification ranges attributed to Tomiyama remain background.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 12, Example (new estimates) 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Example 3.6 (new estimates), PDF pp.12–13. The classification ranges expressly
attributed to Tomiyama are background; this statement retains the new calculations. -/
theorem example_3_6 (hd : 1 < Fintype.card I) :
    let d : ℝ := Fintype.card I
    (∃ e : ℝ, SchwarzBound ⊤ (transposeNoise (I := I) e) 1 ∧
      ¬ AlgebraKPositive ⊤ (transposeNoise (I := I) e) 2) ∧
    (∀ e ∈ Ico (0 : ℝ) 1, ∀ c ≥ (0 : ℝ), ∀ X : Mat I,
      (c : ℂ) • transposeNoise e (Xᴴ * X) - transposeNoise e (Xᴴ) * transposeNoise e X =
        transposeDefect e c X ∧
      LE (((c * e - d * (1 - e) ^ 2 - 2 * e * (1 - e) * Real.sqrt d - e ^ 2) / d : ℂ) •
        (tr (Xᴴ * X) : ℂ) • (1 : Mat I))
        ((c : ℂ) • transposeNoise e (Xᴴ * X) -
          transposeNoise e (Xᴴ) * transposeNoise e X)) ∧
    (∀ e ∈ Ioo (0 : ℝ) 1, AlgebraSchwarzMap ⊤ (transposeNoise (I := I) e) ∧
      ENNReal.ofReal (d * (1 - e) ^ 2 / e) ≤ snorm ⊤ (transposeNoise (I := I) e) ∧
      snorm ⊤ (transposeNoise (I := I) e) ≤ ENNReal.ofReal
        ((d * (1 - e) ^ 2 + 2 * e * (1 - e) * Real.sqrt d + e ^ 2) / e)) ∧
    (∀ e ∈ Ioo (0 : ℝ) 1, ∀ i j : I, i ≠ j →
      let X : Mat I := Matrix.single i j 1
      let S := (((snorm ⊤ (transposeNoise (I := I) e)).toReal : ℂ) • transposeNoise e (Xᴴ * X) -
        transposeNoise e (Xᴴ) * transposeNoise e X) i i
      0 ≤ S.re ∧ S.re = (snorm ⊤ (transposeNoise (I := I) e)).toReal * e / d - (1 - e) ^ 2) ∧
    Tendsto (fun e : ℝ => snorm ⊤ (transposeNoise (I := I) e)) (𝓝[>] 0) (𝓝 ⊤) ∧
    (∀ e ∈ Icc (0 : ℝ) (1 + 1 / (d - 1)), pnorm (transposeNoise (I := I) e) = 1) ∧
    (∀ e ∈ Ioo (0 : ℝ) 1, d < (1 - e) ^ 2 / e →
      ENNReal.ofReal (pnorm (transposeNoise (I := I) e)) < snorm ⊤ (transposeNoise (I := I) e)) ∧
    (∀ e : ℝ, AlgebraSchwarzMap ⊤ (identityNoise (I := I) e) ↔ 0 ≤ e ∧ e < 1 + 1 / (d - 1)) ∧
    Tendsto (fun e : ℝ => snorm ⊤ (identityNoise (I := I) e))
      (𝓝[<] (1 + 1 / (d - 1))) (𝓝 ⊤) ∧
    (∀ e c : ℝ, ∀ i j : I, i ≠ j →
      let X : Mat I := Matrix.single i j 1
      let D : Mat I := (c : ℂ) • transposeMix e (Xᴴ * X) -
        transposeMix e (Xᴴ) * transposeMix e X
      (D i i).re = -(1 - e) ^ 2) ∧
    (∀ e : ℝ, AlgebraSchwarzMap ⊤ (transposeMix (I := I) e) ↔ e = 1) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
