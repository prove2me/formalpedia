-- Prove2me | Theorems.Thm_SchattenSketch_Main_lemma_4_5
-- name    : SchattenSketch.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:57:48.081064+00:00
-- url     : https://prove2.me/theorems/8d547f3a-b138-424f-8172-58eee072a175
-- title:
--   Lemma 4.5 — Gaussian smoothing keeps the nuclear-norm gap with probability $1-\zeta$, and $LX_b=aLF_b+\sigma G_k$ with $G_k\sim N(0,I_k)$ independent of $(U,V)$
-- statement:
--   Let $D_0,D_1$ be $n\times n$ diagonal matrices with nonnegative entries, $m_b=n^{-1}\mathrm{tr}\,D_b$, $F_b=\sqrt n\,UD_bV^\top$ and $X_b=aF_b+\sigma Z$, where $a,\sigma>0$, $U,V$ are Haar distributed on $O_n$ and $Z$ has independent $N(0,1)$ entries, all independent. Let $0<\varepsilon<1$, suppose $(m_1-m_0)/(m_1+m_0)\ge\varepsilon+\eta$, and let $0<\zeta<1$. If
--   $$\frac\sigma a\le\frac{\eta(m_0+m_1)\sqrt\zeta}8,$$
--   then there are deterministic intervals $I_0,I_1\subseteq[0,\infty)$ with $P\{\|X_b\|_{S_1}\in I_b\}\ge 1-\zeta$ for $b=0,1$ and $(1\pm\varepsilon)I_0\cap(1\pm\varepsilon)I_1=\varnothing$. Moreover, for every row coisometry $L$ with $k$ rows,
--   $$LX_b=aLF_b+\sigma G_k,\qquad G_k=LZ\sim N(0,I_k),$$
--   and $G_k$ is independent of $(U,V)$.
--
--   The lemma supplies the separated nuclear-norm ranges required by Lemma 4.1 for the smoothed hard laws $\Pi_b=\mathrm{Law}(X_b)$.
--
--   **Formalization Note.** $D_b=\mathrm{diag}(d_b)$ with $d_b\ge 0$; the probability space is `haarO n ⊗ haarO n ⊗ gaussianMatrix n n` on $(U,V,Z)$; "intervals" are order-connected sets. Independence is `IndepFun` of $(U,V)$ and $LZ$.
--
--   Differences from the source:
--   - reading: ε, η as in §4 (ε the fixed accuracy, 0 < ε < 1) → hypotheses 0 < ε < 1; η unrestricted; reason: §4 fixes 0 < ε < 1 (Theorem 1.1); η > 0 already follows from σ, a > 0 and (4.20)
--   - generalization: D_b = diag(√x_1(b), …, √x_n(b)), the endpoints of the Lemma 4.4 path (p. 17); m_b = n⁻¹ tr D_b → any vectors d_b ≥ 0, D_b = diag d_b, m_b = (1/n) Σ_i d_b i; reason: the lemma and its proof (A.2) use only that D_b is a nonnegative diagonal matrix (so ‖F_b‖_{S_1} = n^{3/2} m_b is deterministic); every path endpoint is such a vector, so the item specializes to the source
--   - encoding: U, V Haar on O_n, Z with i.i.d. N(0,1) entries, all independent → product measure haarO n ⊗ haarO n ⊗ gaussianMatrix n n; reason: the joint law of independent variables
--   - reading: the nuclear norms lie in deterministic intervals whose (1 ± ε) enlargements are disjoint → ∃ I_0 I_1 ⊆ [0, ∞), order-connected, chosen before ω, with the probability bounds and disjoint enlargements; reason: the enlargement is defined for subsets of [0, ∞) (Lemma 4.1), and the proof's intervals [max{0, N_b − r}, N_b + r] are such
--   - reading: LX_b = aLF_b + σG_k, G_k ∼ N(0, I_k), independent of (U, V) → G_k := LZ; for all ω the identity, Law(LZ) = stdGaussian k, IndepFun (U, V) (LZ); reason: G_k is LZ in (4.21) and in the proof (A.2)
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 18, Lemma 4.5, (4.20)–(4.21) (setting p. 17, (4.18)–(4.19); proof pp. 36–37, A.2)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_FourierRankQLB_Od
import Definitions.Def_FourierRankQLB_haarO
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SchattenSketch_Main_Sketch
import Definitions.Def_SchattenSketch_Main_Testing
import Definitions.Def_SchattenSketch_Main_HardModel

open MeasureTheory ProbabilityTheory WainwrightHDS.NucNorm FourierRankQLB GaussianMatrix

namespace SchattenSketch.Main

/-- Lemma 4.5 (smoothing preserves the norm gap; Yang, p. 18). Let `D_b = diag(d_b)`, `b ∈ {0, 1}`,
have nonnegative entries, `m_b = n⁻¹ tr D_b`, `F_b = √n U D_b Vᵀ` and `X_b = a F_b + σ Z` with
`U, V` Haar on `O_n` and `Z` a standard Gaussian `n × n` matrix, all independent, and `a, σ > 0`.
If `(m₁ - m₀)/(m₁ + m₀) ≥ ε + η`, `0 < ζ < 1` and `σ/a ≤ η (m₀ + m₁) √ζ / 8`, then there are
deterministic intervals `I₀, I₁ ⊆ [0, ∞)` with `P{‖X_b‖_{S₁} ∈ I_b} ≥ 1 - ζ` for both labels and
disjoint `(1 ± ε)` enlargements; and for every row coisometry `L`,
`L X_b = a L F_b + σ G_k` where `G_k = L Z` is `N(0, I_k)` and independent of `(U, V)`. -/
theorem lemma_4_5 (n : ℕ) (d₀ d₁ : Fin n → ℝ) (hd₀ : ∀ i, 0 ≤ d₀ i) (hd₁ : ∀ i, 0 ≤ d₁ i)
    (ε η ζ a σ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (ha : 0 < a) (hσ : 0 < σ)
    (hgap : ((1 / (n : ℝ)) * ∑ i, d₁ i - (1 / (n : ℝ)) * ∑ i, d₀ i) /
        ((1 / (n : ℝ)) * ∑ i, d₁ i + (1 / (n : ℝ)) * ∑ i, d₀ i) ≥ ε + η)
    (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (h420 : σ / a ≤ η * ((1 / (n : ℝ)) * ∑ i, d₀ i + (1 / (n : ℝ)) * ∑ i, d₁ i) *
        Real.sqrt ζ / 8) :
    let μ : Measure (Od n × Od n × (Fin n → Fin n → ℝ)) :=
      (haarO n).prod ((haarO n).prod (gaussianMatrix n n))
    let X : (Fin n → ℝ) → Od n × Od n × (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
      fun d ω => a • rotDiag ω.1 ω.2.1 d + σ • Matrix.of ω.2.2
    (∃ I₀ I₁ : Set ℝ, I₀ ⊆ Set.Ici 0 ∧ I₁ ⊆ Set.Ici 0 ∧ I₀.OrdConnected ∧ I₁.OrdConnected ∧
      ENNReal.ofReal (1 - ζ) ≤ μ {ω | nucNorm (X d₀ ω) ∈ I₀} ∧
      ENNReal.ofReal (1 - ζ) ≤ μ {ω | nucNorm (X d₁ ω) ∈ I₁} ∧
      Disjoint (enlarge ε I₀) (enlarge ε I₁)) ∧
    ∀ (k : ℕ) (L : Fin k → Fin n × Fin n → ℝ), IsRowCoisometry L →
      (∀ ω, ∀ d ∈ ({d₀, d₁} : Set (Fin n → ℝ)),
        sketchApply L (X d ω) =
          a • sketchApply L (rotDiag ω.1 ω.2.1 d) + σ • sketchApply L (Matrix.of ω.2.2)) ∧
      μ.map (fun ω => sketchApply L (Matrix.of ω.2.2)) = stdGaussian k ∧
      IndepFun (fun ω => (ω.1, ω.2.1)) (fun ω => sketchApply L (Matrix.of ω.2.2)) μ := by sorry

end SchattenSketch.Main
