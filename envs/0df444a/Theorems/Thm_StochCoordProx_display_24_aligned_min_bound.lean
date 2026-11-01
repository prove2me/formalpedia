-- Prove2me | Theorems.Thm_StochCoordProx_display_24_aligned_min_bound
-- name    : StochCoordProx.display_24_aligned_min_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:05.432553+00:00
-- url     : https://prove2.me/theorems/6615b946-ad6a-49ea-ab24-1b9ffb47e57e
-- title:
--   (24) — $|\mathbb A_K|\min_{0\le i\le K}\|\nabla F(x_i)\|^2\le\frac1C(F(x_0)-F^*)$
-- statement:
--   Let $F=f+\psi$ satisfy Assumption 1 ($f$ differentiable and $L_U$ smooth along every $U\in\mathcal U$, $\psi$ twice continuously differentiable, a minimizer $x^*$ with $F^*=F(x^*)$), let $\mathcal L_F(x_0)$ be bounded and $\alpha\in(0,1)$. Let $(U_k,\eta_k,x_k,d_k)$ be a run of SCPG from $x_0$. Let $\eta_{\min},H_{F,\max}>0$ with $\eta_{\min}\le\eta_{U_k}$ and $H_{F,U_k}\le H_{F,\max}$ for all $k$, and
--
--   $$
--   C=\frac{\alpha^2\eta_{\min}}{2H_{F,\max}^2}.
--   $$
--
--   Let $\mathbb A_K$ be the set of $k\in\{0,\dots,K\}$ at which $U_k$ is well-aligned, $\|U_k^T\nabla F(x_k)\|\ge\alpha\|\nabla F(x_k)\|$. Then on every outcome and for every $K\ge0$
--
--   $$
--   |\mathbb A_K|\min_{0\le i\le K}\|\nabla F(x_i)\|^2\le\frac1C\bigl(F(x_0)-F^*\bigr).
--   $$
--
--   This deterministic inequality reduces Theorem 1 to a lower bound on $|\mathbb A_K|$, which Lemma 6 supplies.
--
--   Differences from the source:
--   - generalization: η_min = min_{k∈ℕ} η_{U_k} and a constant H_{F,max} ≥ H_{F,U_k} (21) → functions ηmin, Hmax : Ω → ℝ with ηmin(ω) ≤ η_k(ω) and H_{F,U_k(ω)} ≤ Hmax(ω) for all k, ω; C(ω) = α²ηmin(ω)/(2Hmax(ω)²); reason: constant bounds and the pathwise min/max (when finite) are instances
--   - encoding: C = α²η_min/(2H²_{F,max}) with η_min, H_{F,max} unrestricted in sign → 0 < ηmin(ω) and 0 < Hmax(ω); reason: excludes only the cases in which C is undefined or not positive (division by zero), where (22) and (24) have no meaning
--   - generalization: η_{U_k} > 0 chosen as a function of U_k → η_k(ω) > 0, any positive choice at step k on outcome ω; reason: Algorithm 1 leaves the choice to the user; a choice depending only on U_k is an instance
--   - generalization: U_k ∼ 𝒰 randomly sampled from a distribution on 𝒰 → any U_k(ω) ∈ 𝒰 on each outcome ω, no distribution fixed; reason: the randomness enters the analysis only through Assumption 2, which is a hypothesis where it is used
--   - generalization: 𝒰 bounded (standing assumption, p.4) → not assumed; reason: used only to make H_{F,max} finite, which is a hypothesis of the statement; every bounded 𝒰 is an instance
--   - generalization: Assumption 2 (part of the hypotheses of Theorem 1) → not assumed; reason: (24) holds on every outcome; Assumption 2 is used only afterwards, through Lemma 6
--   - reading: 𝓛_f(x₀) → 𝓛_F(x₀) = {y : F(y) ≤ F(x₀)}; reason: the only sublevel set the paper defines (p.7); (18) and the proof of Lemma 5 use conv(𝓛_F(x₀)); boundedness of {f ≤ f(x₀)} would not make H_{F,U} finite
--   - encoding: H_{F,U_k} ≤ H_{F,max}, with H_{F,U_k} the max in (18) → IsCurvBound: ‖U_kᵀ∇̄²Ψ(z)U_k + H_{f,U_k}I‖_F ≤ Hmax for all z₁,…,zₙ ∈ conv 𝓛_F(x₀); reason: a max is ≤ B iff every value is ≤ B; avoids a real sSup
--   - generalization: f is L_U smooth along U (A.1) → f differentiable on ℝⁿ and (2) for U with constant L_U; reason: the paper defines the term by (2) and uses nothing else; any smooth f satisfying (2) is an instance
--   - encoding: ψ is simple (A.2) → not stated; reason: a computational remark (the prox of ψ along U is cheap), not a mathematical condition
--   - encoding: A.3: a solution of (1) exists, F* = min F → a point x* with F(x*) ≤ F(y) for all y; F* written F(x*); reason: the same hypothesis; F* is the value at a minimizer
--   - encoding: min_{0≤i≤K} → Finset.inf' over {0,…,K}; reason: the same minimum over K + 1 iterates
--   - encoding: vectors of ℝⁿ, ℝᵖ and matrices U ∈ ℝ^{n×p} → EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin p), U acting through Matrix.toEuclideanLin; reason: Lean convention; the Euclidean norm and inner product of the paper, same instances
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, proof of Theorem 1, display (24), p.11

import Mathlib
import Definitions.Def_StochCoordProx_IsSmoothAlong
import Definitions.Def_StochCoordProx_IsSCPGRun
import Definitions.Def_StochCoordProx_WellAligned
import Definitions.Def_StochCoordProx_IsCurvBound
import Definitions.Def_StochCoordProx_alignedCount

namespace StochCoordProx

/-- **Display (24)** (proof of Theorem 1): for an SCPG run from `x₀` under Assumption 1 (`f`
differentiable and `L_U` smooth along every `U ∈ 𝒰`, `ψ` twice continuously differentiable, a
minimizer `x*` of `F = f + ψ`, `F* = F(x*)`), with `𝓛_F(x₀)` bounded and `α ∈ (0,1)`, let
`η_min, H_{F,max} > 0` satisfy `η_min ≤ η_{U_k}` and `H_{F,U_k} ≤ H_{F,max}` for all `k` (21), and
`C = α² η_min / (2 H²_{F,max})`. Then for every `K ≥ 0`
`|𝔸_K| · min_{0≤i≤K} ‖∇F(xᵢ)‖² ≤ (1/C)(F(x₀) − F*)`  (24),
where `𝔸_K` is the set of `k ∈ {0, …, K}` at which `U_k` is well-aligned (14).

Necoara & Chorobura, arXiv:2104.13370v3, proof of Theorem 1, display (24), p.11.

**Formalization Note.** Pathwise on each outcome `ω`. `η_min` and `H_{F,max}` are functions of
`ω` (constants are a special case); their positivity only excludes the cases where `C` is
undefined. `H_{F,U_k} ≤ H_{F,max}` is `IsCurvBound … (Hmax ω)` with `H = H_{f,U_k}`. The minimum
over `0 ≤ i ≤ K` is `Finset.inf'` over `Finset.range (K + 1)`. Assumption 2 is not used. -/
theorem display_24_aligned_min_bound {n p : ℕ} {Ω : Type*}
    (f ψ : EuclideanSpace ℝ (Fin n) → ℝ) (𝒰 : Set (Matrix (Fin n) (Fin p) ℝ))
    (L : Matrix (Fin n) (Fin p) ℝ → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hf : Differentiable ℝ f) (hL : ∀ V ∈ 𝒰, IsSmoothAlong f V (L V)) (hψ : ContDiff ℝ 2 ψ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : ∀ y, f xstar + ψ xstar ≤ f y + ψ y)
    (hbdd : Bornology.IsBounded {y : EuclideanSpace ℝ (Fin n) | f y + ψ y ≤ f x₀ + ψ x₀})
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (U : ℕ → Ω → Matrix (Fin n) (Fin p) ℝ) (η : ℕ → Ω → ℝ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (d : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsSCPGRun f ψ 𝒰 L x₀ U η x d)
    (ηmin Hmax : Ω → ℝ) (hηmin_pos : ∀ ω, 0 < ηmin ω) (hηmin : ∀ ω k, ηmin ω ≤ η k ω)
    (hHmax_pos : ∀ ω, 0 < Hmax ω)
    (hHmax : ∀ ω k, IsCurvBound f ψ x₀ (U k ω) (Hf ψ 𝒰 (L (U k ω)) (η k ω)) (Hmax ω))
    (ω : Ω) (K : ℕ) :
    (alignedCount (fun k => {ω' : Ω | WellAligned α (gradient (fun y => f y + ψ y) (x k ω'))
        (U k ω')}) K ω : ℝ) *
        (Finset.range (K + 1)).inf' Finset.nonempty_range_add_one
          (fun i => ‖gradient (fun y => f y + ψ y) (x i ω)‖ ^ 2) ≤
      1 / (α ^ 2 * ηmin ω / (2 * Hmax ω ^ 2)) * ((f x₀ + ψ x₀) - (f xstar + ψ xstar)) := by sorry

end StochCoordProx
