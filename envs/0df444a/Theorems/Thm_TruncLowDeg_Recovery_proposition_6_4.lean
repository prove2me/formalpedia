-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_proposition_6_4
-- name    : TruncLowDeg.Recovery.proposition_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:25:35.701358+00:00
-- url     : https://prove2.me/theorems/d947522e-d173-4e46-a495-58ebb3a7143d
-- title:
--   Proposition 6.4 — every solution of (14) satisfies $\|p_js_j-q_j\|_{L^2(U)}\le\eta\,(d/\alpha_0)^{O(k)}$
-- statement:
--   In the setting of Theorem 6.1, assume that the preconditioning succeeds and (15) holds. Then every solution $(p_j,q_j)\in\mathbb R[x]_{\le3k}\times\mathbb R[x]_{\le4k}$ to (14) satisfies
--   $$\|p_js_j-q_j\|_{L^2(U)}\le\eta\cdot(d/\alpha_0)^{O(k)} .$$
--   Formally: for every constant $C_4>0$ of Lemma 5.4, every $\rho$-constant $c_\rho\ge1$ and all constants $c_q,c_r$ of (14) there is $C>0$ such that for all $d,k\ge1$, $\alpha_0\in(0,1]$, $\varepsilon\in(0,1)$, any $\eta$-constant, every $\mu,\Sigma,S,\hat{\mathcal D}$ with the preconditioning succeeding, $S\subseteq\{\|x\|_2\le\rho\}$ and (15), every $j$ and every solution $(p_j,q_j)$ of (14), $\|p_js_j-q_j\|_{L^2(U)}\le\eta\,(d/\alpha_0)^{Ck}$. This is the identifiability step: any feasible pair of (14), not only the planted $(g,gs_j)$, reveals $s_j$ up to the error $\eta(d/\alpha_0)^{O(k)}$.
--
--   Differences from the source:
--
--   - generalization: (d/α₀)^{O(k)} in the conclusion, and the implicit constants of (14), ρ and Lemma 5.4 → ∀ C₄ > 0, ∀ c_ρ ≥ 1, ∀ c_q, c_r, ∃ C > 0 such that the bound η·(d/α₀)^{C·k} holds for every c_η, d, k, α₀, ε and instance; reason: C depends only on the constants of (14), of ρ and of Lemma 5.4, as in the proof; every C₄ > 0, c_ρ ≥ 1 and c_q, c_r are covered, including the paper's, so it specializes
--   - generalization: the objects of the setting of Theorem 6.1: µ = Σ̂_pre^{−1/2}(µ₀ − µ̂_pre), Σ = Σ̂_pre^{−1/2}Σ₀Σ̂_pre^{−1/2}, S = T(S₀) ∩ {‖x‖₂ ≤ ρ} and the clipped data 𝒟̂ → arbitrary µ, Σ, S and a finite list 𝒟̂ such that the preconditioning succeeds (`Success`: Lemma 5.4's conclusions with constant C₄, N(µ, Σ)(S) ≥ α₀/2, BVD(S) ≤ 3k), S ⊆ {‖x‖₂ ≤ ρ} and (15) holds; reason: the statement is deterministic in these objects (its hypotheses are conditions on them, not a probability event); the setting's objects satisfy the hypotheses, so it specializes
--   - generalization: "(15) holds", whose display (p. 27) also contains the retention inequality |𝒟̂| ≥ |𝒟̂_rec|/4 → only the concentration inequality (`Eq15`); the retention inequality is dropped; reason: the deterministic statement has no 𝒟̂_rec and the proof does not use the retained count; with it the statement specializes
--   - encoding: sup over 0 ≠ f ∈ ℝ[x]_{≤10k} of |E_𝒟̂[f q_j − ∂_j(f p_j)]| / ‖f‖_{L²(U)} ≤ B in (14) → |E_𝒟̂[f q_j − ∂_j(f p_j)]| ≤ B ‖f‖_{L²(U)} for every f of total degree ≤ 10k (`Solves14`); reason: equivalent: ‖f‖_{L²(U)} > 0 for f ≠ 0 and both sides vanish at f = 0
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 27, Proposition 6.4; proof pp. 30–31 (§6.1.2)

import Definitions.Def_TruncLowDeg_Recovery_Algorithm

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Proposition 6.4 (p. 27): every solution of (14) is close to `(p_j, p_j s_j)`. For every
constant `C₄` of Lemma 5.4, every `ρ`-constant `cρ ≥ 1` and every pair of constants `c_q, c_r`
of (14) there is `C > 0` (the `O(k)`) such that: for `d, k ≥ 1`, `α₀ ∈ (0, 1]`, `ε ∈ (0, 1)`,
any `η`-constant, `ρ = cρ √d/α₀²`, `η = ε (α₀/d)^{c_η k}`, any `µ`, `Σ`, `S`, `𝒟̂` such that the
preconditioning succeeds, `S ⊆ {‖x‖₂ ≤ ρ}` and (15) holds, every solution `(p_j, q_j)` of (14)
satisfies `‖p_j s_j − q_j‖_{L²(U)} ≤ η (d/α₀)^{Ck}`. -/
theorem proposition_6_4 :
    ∀ C₄ : ℝ, 0 < C₄ → ∀ cρ cq cr : ℕ, 1 ≤ cρ → ∃ C : ℝ, 0 < C ∧
      ∀ c : Consts, c.rho = cρ → c.q = cq → c.r = cr →
      ∀ (d k : ℕ) (α₀ ε : ℝ), 1 ≤ d → 1 ≤ k → 0 < α₀ → α₀ ≤ 1 → 0 < ε → ε < 1 →
      ∀ (μ : Vec d) (Sig : Mat d) (S : Set (Vec d)) (D : List (Vec d)),
        Success C₄ k α₀ μ Sig S → S ⊆ Metric.closedBall 0 (rhoV c d α₀) →
        Eq15 k (rhoV c d α₀) (etaV c d k α₀ ε) D μ Sig S →
        ∀ (j : Fin d) (p q : MvPolynomial (Fin d) ℝ),
          Solves14 k α₀ (rhoV c d α₀) (etaV c d k α₀ ε) c.q c.r D j p q →
          L2U (rhoV c d α₀) (p * sPoly μ Sig j - q) ≤
            etaV c d k α₀ ε * ((d : ℝ) / α₀) ^ (C * k) := by sorry

end TruncLowDeg.Recovery
