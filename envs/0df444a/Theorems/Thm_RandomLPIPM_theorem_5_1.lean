-- Prove2me | Theorems.Thm_RandomLPIPM_theorem_5_1
-- name    : RandomLPIPM.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:09.052608+00:00
-- url     : https://prove2.me/theorems/95a97250-5983-4cf4-8372-0213cf747e44
-- title:
--   Theorem 5.1 — Gaussian projection bound: $\max_{w\in\mathcal C}|w^\top\Pi b|=O(M\log^3N)$ w.h.p.
-- statement:
--   Fix $c\in(0,1/2]$. Let $N$ be large, $T\succeq0$ a deterministic $N\times N$ matrix, and $m$ an integer with $cN\le m\le\operatorname{rank}(T)-cN$. Let $G\in\mathbb R^{m\times N}$ have independent $\mathcal N(0,1)$ entries and $\Pi=T^{1/2}G^\top(GTG^\top)^{-1}GT^{1/2}$. Let $b\in\mathbb R^N$ be deterministic, $\mathcal C\subseteq\mathbb R^N$ a deterministic set of at most $N$ unit vectors, and $t_0>0$ with $f_T(t_0)\ge m+\tfrac c2N$. Suppose that for some $M\ge1$:
--   1. (bias, (24)) $|w^\top F_T(t)b|\le M$ for all $w\in\mathcal C$, $0<t\le t_0$;
--   2. (narrow window, (25)) $(w^\top H_T(t)w)(b^\top H_T(t)b)\le M^2(1+h_T(t))$ for all $w\in\mathcal C$, $0<t\le t_0$;
--   3. (wide window, (26)) $b^\top(F_T(t_1)-F_T(t_2))b\le M^2(1+f_T(t_1)-f_T(t_2))$ for all $0<t_2\le t_1\le t_0$.
--
--   Then for every $q>0$ there are $K>0$ and $N_0$, depending only on $c$ and $q$, such that for $N\ge N_0$
--   $$\Pr\Big[\max_{w\in\mathcal C}|w^\top\Pi b|>K\,M\log^3N\Big]\le N^{-q}.$$
--
--   This is the probabilistic engine of the paper: it bounds Gaussian projections in every direction of $\mathcal C$ at once under spectral conditions that survive rank-one perturbations of $T$.
--
--   **Formalization Note** $T^{1/2}$ is the PSD square root; the total matrix inverse makes $\Pi=0$ on a null event. The paper's letter $c$ for the vectors of $\mathcal C$ is renamed $w$.
--
--   Differences from the source:
--   - reading: with high probability, O(M log³ N) → ∀ q > 0 ∃ K > 0, N₀ (depending only on c, q) such that for N ≥ N₀ the probability that some w ∈ 𝒞 has |wᵀΠb| > K·M·log³N is ≤ N^(−q); reason: the paper's definition of w.h.p. (p.21) with the failure exponent arbitrary, as its proofs deliver (p.56, p.81)
--   - encoding: a deterministic set 𝒞 of at most N unit vectors, vectors named c → a Finset W of vectors with w ⬝ᵥ w = 1 and card ≤ N, vectors named w; reason: c is also the constant; same sets
--   - encoding: T^{1/2}, (GTGᵀ)⁻¹ → CFC.sqrt T (PSD square root), total matrix inverse; reason: Π is only changed on the null event that GTGᵀ is singular
--   - encoding: probability of the event → outer Gaussian measure of the failure set bounded by the failure probability; reason: no measurability assumption is needed; for a measurable event it is 1 − P(event)
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 5.1, p.33

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_matF
import Definitions.Def_RandomLPIPM_matH
import Definitions.Def_RandomLPIPM_traceF
import Definitions.Def_RandomLPIPM_traceH
import Definitions.Def_RandomLPIPM_gaussProj

open Matrix MeasureTheory

namespace RandomLPIPM

/-- **Theorem 5.1 (Gaussian Projection Bound).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 5.1, p.33.

Fix `c ∈ (0, 1/2]`. For `N` large, let `T ⪰ 0` be a deterministic `N × N` matrix, `m` an integer with
`cN ≤ m ≤ rank(T) − cN`, `G ∈ ℝ^{m×N}` with independent `N(0,1)` entries,
`Π = T^{1/2}Gᵀ(GTGᵀ)⁻¹GT^{1/2}`, `b ∈ ℝᴺ` deterministic, `𝒞` a deterministic set of at most `N`
unit vectors, and `t₀ > 0` with `f_T(t₀) ≥ m + (c/2)N`. If for some `M ≥ 1` the bias condition (24),
the narrow-window variance condition (25) (for all `w ∈ 𝒞`, `0 < t ≤ t₀`) and the wide-window
variance condition (26) (for all `0 < t₂ ≤ t₁ ≤ t₀`) hold, then w.h.p. `max_{w∈𝒞} |wᵀΠb| ≤ O(M log³ N)`.

**Formalization Note.** "With high probability" and `O(·)`: for every exponent `q > 0` there are a
constant `K > 0` and a threshold `N₀`, depending only on `c` and `q` (not on `T, m, b, 𝒞, t₀, M`),
such that for `N ≥ N₀` the failure probability is at most `N^{−q}` (p.21). The failure set is
measured by the (outer) Gaussian measure. The paper's letter `c` for the vectors of `𝒞` is renamed
`w`. -/
theorem theorem_5_1 :
    ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → ∀ q : ℝ, 0 < q →
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ T : Matrix (Fin N) (Fin N) ℝ, T.PosSemidef →
    ∀ m : ℕ, c * N ≤ m → (m : ℝ) ≤ (T.rank : ℝ) - c * N →
    ∀ (b : Fin N → ℝ) (W : Finset (Fin N → ℝ)), (∀ w ∈ W, w ⬝ᵥ w = 1) → W.card ≤ N →
    ∀ t₀ : ℝ, 0 < t₀ → (m : ℝ) + c / 2 * N ≤ traceF T t₀ →
    ∀ M : ℝ, 1 ≤ M →
    (∀ w ∈ W, ∀ t : ℝ, 0 < t → t ≤ t₀ → |w ⬝ᵥ (matF T t *ᵥ b)| ≤ M) →
    (∀ w ∈ W, ∀ t : ℝ, 0 < t → t ≤ t₀ →
      (w ⬝ᵥ (matH T t *ᵥ w)) * (b ⬝ᵥ (matH T t *ᵥ b)) ≤ M ^ 2 * (1 + traceH T t)) →
    (∀ t₁ t₂ : ℝ, 0 < t₂ → t₂ ≤ t₁ → t₁ ≤ t₀ →
      b ⬝ᵥ ((matF T t₁ - matF T t₂) *ᵥ b) ≤ M ^ 2 * (1 + traceF T t₁ - traceF T t₂)) →
    GaussianMatrix.gaussianMatrix m N
      {G | ∃ w ∈ W, K * M * Real.log N ^ 3 < |w ⬝ᵥ (gaussProj T (Matrix.of G) *ᵥ b)|} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-q)) := by sorry

end RandomLPIPM
