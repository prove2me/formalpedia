-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_lemma_6_3
-- name    : TruncLowDeg.Recovery.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:25:44.902082+00:00
-- url     : https://prove2.me/theorems/14b100b5-4e3b-4ed3-87ad-ab1796ab46d3
-- title:
--   Lemma 6.3 — feasibility of (14): $(g, g s_j)$ solves (14) for a normalized boundary vanishing $g$
-- statement:
--   In the setting of Theorem 6.1 write $s_j(x)=(\Sigma^{-1}(x-\mu))_j$ and assume that the preconditioning succeeds and
--   $$|\hat{\mathcal D}|\ge|\hat{\mathcal D}_{rec}|/4,\qquad \big|\mathbb E_{\hat{\mathcal D}}[f(X)]-\mathbb E_{X\sim\mathcal N(\mu,\Sigma)|_S}[f(X)]\big|\le\eta\,\|f\|_{L^2(U)}\quad\forall f\in\mathbb R[x]_{\le14k}. \tag{15}$$
--   Let $g\in\mathbb R[x]_{\le3k}$ satisfy $g|_{\partial S}\equiv0$ and $\|g\|_{L^2(U)}=1$. Then $(g,gs_j)$ is a solution to (14).
--
--   Formally: for every constant $C_4>0$ of Lemma 5.4 and every $\rho$-constant $c_\rho\ge1$ there is $N$ such that, whenever both constants of (14) are at least $N$, for all $d,k\ge1$, $\alpha_0\in(0,1]$, $\varepsilon\in(0,1)$, $\rho=c_\rho\sqrt d/\alpha_0^2$, $\eta=\varepsilon(\alpha_0/d)^{c_\eta k}$, every $\mu,\Sigma,S$ and finite list $\hat{\mathcal D}$ with the preconditioning succeeding, $S\subseteq\{\|x\|_2\le\rho\}$ and (15), every $j$ and every such $g$, the pair $(g,gs_j)$ satisfies (14). This makes line 9 of Algorithm 1 feasible on the good event. As printed it fails at $d=\alpha_0=1$ (finding I4).
--
--   Differences from the source:
--
--   - generalization: "for sufficiently large implicit constants in (14)"; the constant of Lemma 5.4 in "the preconditioning succeeds"; ρ's constant → ∀ C₄ > 0, ∀ c_ρ ≥ 1, ∃ N, ∀ c with c_q ≥ N and c_r ≥ N (c_pre, c_η arbitrary); reason: the paper's dependency order; every C₄ > 0 and every c_ρ ≥ 1 are covered, including Lemma 5.4's constant and the paper's sufficiently large ρ-constant, so it specializes; c_ρ ≥ 1 gives ρ ≥ 1, which the proof needs for Lemma 5.7
--   - generalization: the objects of the setting of Theorem 6.1: µ = Σ̂_pre^{−1/2}(µ₀ − µ̂_pre), Σ = Σ̂_pre^{−1/2}Σ₀Σ̂_pre^{−1/2}, S = T(S₀) ∩ {‖x‖₂ ≤ ρ} and the clipped data 𝒟̂ → arbitrary µ, Σ, S and a finite list 𝒟̂ such that the preconditioning succeeds (`Success`: Lemma 5.4's conclusions with constant C₄, N(µ, Σ)(S) ≥ α₀/2, BVD(S) ≤ 3k), S ⊆ {‖x‖₂ ≤ ρ} and (15) holds; reason: the statement is deterministic in these objects (its hypotheses are conditions on them, not a probability event); the setting's objects satisfy the hypotheses, so it specializes
--   - generalization: the hypothesis |𝒟̂| ≥ |𝒟̂_rec|/4 → dropped; reason: the deterministic statement has no 𝒟̂_rec and the proof does not use the retained count; with it the statement specializes
--   - encoding: sup over 0 ≠ f ∈ ℝ[x]_{≤10k} of |E_𝒟̂[f q_j − ∂_j(f p_j)]| / ‖f‖_{L²(U)} ≤ B in (14) → |E_𝒟̂[f q_j − ∂_j(f p_j)]| ≤ B ‖f‖_{L²(U)} for every f of total degree ≤ 10k (`Solves14`); reason: equivalent: ‖f‖_{L²(U)} > 0 for f ≠ 0 and both sides vanish at f = 0
--   - encoding: g|_{∂S} ≡ 0, s_j as a polynomial → ∀ x ∈ frontier S, peval g x = 0; `sPoly µ Σ j = ∑_i (Σ⁻¹)_{ji} X_i − (Σ⁻¹µ)_j`; reason: the definitions
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 27, Lemma 6.3; proof pp. 29–30 (§6.1.1)

import Definitions.Def_TruncLowDeg_Recovery_Algorithm

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Lemma 6.3 (p. 27): feasibility of (14). For every constant `C₄` of Lemma 5.4 and every
`ρ`-constant `cρ ≥ 1` there is a threshold `N` such that, whenever the two constants of (14)
are at least `N`: for `d, k ≥ 1`, `α₀ ∈ (0, 1]`, `ε ∈ (0, 1)`, `ρ = cρ √d/α₀²`,
`η = ε (α₀/d)^{c_η k}`, any `µ`, `Σ`, `S`, `𝒟̂` such that the preconditioning succeeds
(`Success`), `S ⊆ {‖x‖₂ ≤ ρ}` and (15) holds, any coordinate `j` and any `g ∈ ℝ[x]_{≤3k}` with
`g|_{∂S} ≡ 0` and `‖g‖_{L²(U)} = 1`, the pair `(g, g s_j)` with `s_j(x) = (Σ⁻¹(x − µ))_j`
solves (14). -/
theorem lemma_6_3 :
    ∀ C₄ : ℝ, 0 < C₄ → ∀ cρ : ℕ, 1 ≤ cρ → ∃ N : ℕ,
      ∀ c : Consts, c.rho = cρ → N ≤ c.q → N ≤ c.r →
      ∀ (d k : ℕ) (α₀ ε : ℝ), 1 ≤ d → 1 ≤ k → 0 < α₀ → α₀ ≤ 1 → 0 < ε → ε < 1 →
      ∀ (μ : Vec d) (Sig : Mat d) (S : Set (Vec d)) (D : List (Vec d)),
        Success C₄ k α₀ μ Sig S → S ⊆ Metric.closedBall 0 (rhoV c d α₀) →
        Eq15 k (rhoV c d α₀) (etaV c d k α₀ ε) D μ Sig S →
        ∀ (j : Fin d) (g : MvPolynomial (Fin d) ℝ), g.totalDegree ≤ 3 * k →
          (∀ x ∈ frontier S, peval g x = 0) → L2U (rhoV c d α₀) g = 1 →
          Solves14 k α₀ (rhoV c d α₀) (etaV c d k α₀ ε) c.q c.r D j g
            (g * sPoly μ Sig j) := by sorry

end TruncLowDeg.Recovery
