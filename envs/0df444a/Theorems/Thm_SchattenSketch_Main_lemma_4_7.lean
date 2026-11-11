-- Prove2me | Theorems.Thm_SchattenSketch_Main_lemma_4_7
-- name    : SchattenSketch.Main.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:57:43.48028+00:00
-- url     : https://prove2.me/theorems/b25e8922-e661-4f6b-ac3f-01878e4c9b7b
-- title:
--   Lemma 4.7 — observation comparison along a moment-preserving path: $d_{TV}(P^L_0,P^L_1)\le\frac12A_mn(k/n^2)^{(K+1)/2}L_K$
-- statement:
--   There are absolute constants $C_{ten}\ge 1$ (the constant of Lemma 4.6) and $C_{en}>0$ (the energy constant of Appendix C) with the following property. Let $B\ge 1$, $K\ge 2$, and let $x_1,\dots,x_n:[0,1]\to[0,B]$ be particle paths as supplied by Lemma 4.4: piecewise continuously differentiable after taking square roots, with $\frac1n\sum_ix_i(t)^q$ independent of $t$ for $0\le q\le K$. Put $D_t=\mathrm{diag}(\sqrt{x_1(t)},\dots,\sqrt{x_n(t)})$ and $F_t=\sqrt n\,UD_tV^\top$, let $L$ be a $k\times n^2$ row coisometry, $a,\sigma>0$, and
--   $$Y_t=aLF_t+\sigma G_k,\qquad P^L_t=\mathrm{Law}(Y_t),$$
--   with $U,V$ Haar on $O_n$ and $G_k\sim N(0,I_k)$, all independent. Set $m=2K+1$ and suppose $(4m)^{4m}\le n/2$. Then
--   $$d_{TV}(P^L_0,P^L_1)\le\frac12A_m\,n\Bigl(\frac k{n^2}\Bigr)^{(K+1)/2}L_K,\qquad A_m=\Bigl(\frac a\sigma\Bigr)^m\sqrt{m!}\,(C_{ten}m)^{C_{ten}m/2}(C_{en}B)^{(m-1)/2},$$
--   with $L_K$ the path length (4.10). At the endpoints $P^L_b=\mathrm{Law}(LX_b)=L_\#\Pi_b$, where $X_b=aF_b+\sigma Z$ with $Z$ a standard Gaussian $n\times n$ matrix independent of $(U,V)$.
--
--   Together with Lemmas 4.4–4.6 this gives the small total variation required by Lemma 4.1 once $k\le n^2/(\log n)^{A_\varepsilon}$.
--
--   **Formalization Note.** The probability space is `haarO n ⊗ haarO n ⊗ stdGaussian k` on $(U,V,G_k)$, laws are `Measure.map`, and $d_{TV}$ is `tvDist`. The endpoint identity is stated as a second conjunct: the law of $Y_b$ equals the law of $L(aF_b+\sigma Z)$ under `haarO n ⊗ haarO n ⊗ gaussianMatrix n n`, which is $L_\#\Pi_b$.
--
--   Differences from the source:
--   - generalization: D_t a path supplied by Lemma 4.4 → any paths x_i : [0,1] → [0,B] with B ≥ 1, K ≥ 2, √x_i piecewise C¹ and empirical moments of orders ≤ K constant in t; reason: these are the properties Lemma 4.4 delivers that the proof (p. 22, App. C) uses; every path of Lemma 4.4 satisfies them, so the item specializes to the source
--   - reading: C_ten the constant of Lemma 4.6, C_en the fixed absolute constant of Appendix C → ∃ C_ten ≥ 1, ∃ C_en > 0 chosen before n, K, k, B, a, σ, L and the paths; reason: an item cannot name another item's witness; Lemma 4.6 holds for every larger constant too
--   - encoding: U, V Haar, G_k ∼ N(0, I_k) independent; P^L_t = Law(Y_t); d_TV → product measure haarO n ⊗ haarO n ⊗ stdGaussian k; Measure.map; tvDist; reason: the same laws
--   - encoding: P^L_b = Law(LX_b) = L_#Π_b → Law(Y_b) = map of (U, V, Z) ↦ L(aF_b + σZ) under haarO n ⊗ haarO n ⊗ gaussianMatrix n n; reason: L_#Π_b is by (4.0) the law of LX_b
--   - encoding: m = 2K + 1, (m−1)/2, (K+1)/2, C_ten m/2 exponents → let m := 2K + 1; real powers (rpow); reason: same values
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 21–22, Lemma 4.7, (4.23) (proof p. 22 and App. C)

import Mathlib
import Definitions.Def_FourierRankQLB_Od
import Definitions.Def_FourierRankQLB_haarO
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SchattenSketch_Main_Sketch
import Definitions.Def_SchattenSketch_Main_Testing
import Definitions.Def_SchattenSketch_Main_HardModel
import Definitions.Def_SchattenSketch_Main_Path

open MeasureTheory ProbabilityTheory FourierRankQLB GaussianMatrix

namespace SchattenSketch.Main

/-- Lemma 4.7 (observation comparison along a moment-preserving path; Yang, p. 21). There are
absolute constants `C_ten ≥ 1` and `C_en > 0` such that: let `x₁, …, xₙ : [0, 1] → [0, B]`
(`B ≥ 1`, `K ≥ 2`) be particle paths as supplied by Lemma 4.4 (piecewise `C¹` after square roots,
empirical moments of orders `0, …, K` constant in `t`), `D_t = diag(√x₁(t), …, √xₙ(t))`,
`F_t = √n U D_t Vᵀ`, `L` a `k × n²` row coisometry, `a, σ > 0`, and
`Y_t = a L F_t + σ G_k` with `U, V` Haar on `O_n` and `G_k ∼ N(0, I_k)`, all independent. With
`m = 2K + 1` and `(4m)^{4m} ≤ n/2`,
`d_TV(Law Y₀, Law Y₁) ≤ ½ A_m n (k/n²)^{(K+1)/2} L_K`,
`A_m = (a/σ)^m √(m!) (C_ten m)^{C_ten m/2} (C_en B)^{(m-1)/2}`; and at the endpoints
`Law(Y_b) = Law(L X_b)` with `X_b = a F_b + σ Z`, `Z` a standard Gaussian `n × n` matrix
independent of `(U, V)`. -/
theorem lemma_4_7 :
    ∃ C_ten C_en : ℝ, 1 ≤ C_ten ∧ 0 < C_en ∧
      ∀ (n K k : ℕ) (B a σ : ℝ) (x : Fin n → ℝ → ℝ) (L : Fin k → Fin n × Fin n → ℝ),
        1 ≤ B → 2 ≤ K → 0 < a → 0 < σ → IsRowCoisometry L →
        (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, x i t ∈ Set.Icc 0 B) →
        (∀ i, SqrtPiecewiseC1 (x i)) →
        (∀ q : ℕ, q ≤ K → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          (1 / (n : ℝ)) * ∑ i, x i t ^ q = (1 / (n : ℝ)) * ∑ i, x i 0 ^ q) →
        ((4 * (2 * K + 1) : ℕ) : ℝ) ^ (4 * (2 * K + 1)) ≤ (n : ℝ) / 2 →
        let m : ℕ := 2 * K + 1
        let D : ℝ → Fin n → ℝ := fun t i => Real.sqrt (x i t)
        let ν : Measure (Od n × Od n × (Fin k → ℝ)) :=
          (haarO n).prod ((haarO n).prod (stdGaussian k))
        let Y : ℝ → Od n × Od n × (Fin k → ℝ) → (Fin k → ℝ) := fun t ω =>
          a • sketchApply L (rotDiag ω.1 ω.2.1 (D t)) + σ • ω.2.2
        let A_m : ℝ := (a / σ) ^ m * Real.sqrt (m.factorial : ℝ) *
          (C_ten * m) ^ (C_ten * m / 2) * (C_en * B) ^ (((m : ℝ) - 1) / 2)
        tvDist (ν.map (Y 0)) (ν.map (Y 1)) ≤
            (1 / 2) * A_m * n * ((k : ℝ) / (n : ℝ) ^ 2) ^ (((K : ℝ) + 1) / 2) * pathLength x ∧
        ∀ b ∈ ({0, 1} : Set ℝ),
          ν.map (Y b) =
            ((haarO n).prod ((haarO n).prod (gaussianMatrix n n))).map (fun ω =>
              sketchApply L (a • rotDiag ω.1 ω.2.1 (D b) + σ • Matrix.of ω.2.2)) := by sorry

end SchattenSketch.Main
