-- Prove2me | Theorems.Thm_StochCoordProx_theorem_1_high_prob_rate
-- name    : StochCoordProx.theorem_1_high_prob_rate
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:21.067997+00:00
-- url     : https://prove2.me/theorems/ba4b390a-6c07-4a8e-9a17-dc67bc742e1b
-- title:
--   Theorem 1 — high-probability rate $\min_{0\le i\le K}\|\nabla F(x_i)\|^2\le\frac{F(x_0)-F^*}{C(1-\beta)(1-\delta)(K+1)}$ for SCPG
-- statement:
--   Consider $\min_{x\in\mathbb R^n}F(x)=f(x)+\psi(x)$ under Assumption 1:
--
--   1. $f$ is differentiable and $L_U$ smooth along every $U$ in a family $\mathcal U\subset\mathbb R^{n\times p}$: $\|U^T(\nabla f(x+Uh)-\nabla f(x))\|\le L_U\|h\|$;
--   2. $\psi$ is twice continuously differentiable (possibly nonseparable and nonconvex);
--   3. $F$ has a minimizer $x^*$, $F^*=F(x^*)$.
--
--   Let the sublevel set $\mathcal L_F(x_0)=\{x:F(x)\le F(x_0)\}$ be bounded and let $\alpha,\delta\in(0,1)$. Let $(U_k,\eta_k,x_k,d_k)_{k\ge0}$ be a run of SCPG (Algorithm 1) from $x_0$ on a probability space $(\Omega,P)$ with a filtration $(\mathcal F_k)$, satisfying Assumption 2 for the events $\{U_k\text{ is well-aligned}\}=\{\|U_k^T\nabla F(x_k)\|\ge\alpha\|\nabla F(x_k)\|\}$. Let $\eta_{\min},H_{F,\max}>0$ satisfy $\eta_{\min}\le\eta_{U_k}$ and $H_{F,U_k}\le H_{F,\max}$ for all $k$, with $H_{F,U_k}$ as in (18), and put $C=\alpha^2\eta_{\min}/(2H_{F,\max}^2)$. Then for all $\beta\in(0,1)$ and all $K\ge0$
--
--   $$
--   P\left[\min_{0\le i\le K}\|\nabla F(x_i)\|^2\le\frac{F(x_0)-F^*}{C(1-\beta)(1-\delta)(K+1)}\right]\ge1-e^{-\frac{\beta^2}{2}(1-\delta)(K+1)} .
--   $$
--
--   This is a high-probability $\mathcal O(1/K)$ rate for the squared gradient norm of a stochastic coordinate proximal gradient method in which both $f$ and $\psi$ may be nonconvex and nonseparable, and only proximal steps of $\psi$ along random subspaces are computed.
--
--   **Formalization Note** The probability is stated for the complementary event, $P[\forall i\le K:\ \|\nabla F(x_i)\|^2>\tfrac{F(x_0)-F^*}{C(1-\beta)(1-\delta)(K+1)}]\le e^{-\frac{\beta^2}{2}(1-\delta)(K+1)}$. The quantities $\eta_{\min}$, $H_{F,\max}$ and $C$ may depend on the outcome.
--
--   Differences from the source:
--   - generalization: η_min = min_{k∈ℕ} η_{U_k} and a constant H_{F,max} ≥ H_{F,U_k} (21) → functions ηmin, Hmax : Ω → ℝ with ηmin(ω) ≤ η_k(ω) and H_{F,U_k(ω)} ≤ Hmax(ω) for all k, ω; C(ω) = α²ηmin(ω)/(2Hmax(ω)²); reason: constant bounds and the pathwise min/max (when finite) are instances
--   - encoding: C = α²η_min/(2H²_{F,max}) with η_min, H_{F,max} unrestricted in sign → 0 < ηmin(ω) and 0 < Hmax(ω); reason: excludes only the cases in which C is undefined or not positive (division by zero), where (22) and (24) have no meaning
--   - generalization: η_{U_k} > 0 chosen as a function of U_k → η_k(ω) > 0, any positive choice at step k on outcome ω; reason: Algorithm 1 leaves the choice to the user; a choice depending only on U_k is an instance
--   - generalization: U_k ∼ 𝒰 randomly sampled from a distribution on 𝒰 → any U_k(ω) ∈ 𝒰 on each outcome ω, no distribution fixed; reason: the randomness enters the analysis only through Assumption 2, which is a hypothesis where it is used
--   - generalization: 𝒰 bounded (standing assumption, p.4) → not assumed; reason: used only to make H_{F,max} finite, which is a hypothesis of the statement; every bounded 𝒰 is an instance
--   - reading: Assumption 2: well-aligned with probability at least 1 − δ, independently of the filtration 𝓕_k := {U₀,…,U_{k−1}} → P[W_k | 𝓕_k] ≥ 1 − δ almost surely for W_k = {U_k well-aligned at x_k}; reason: alignment is measured at x_k, which depends on the past; the reading in which the event is independent of 𝓕_k implies this one
--   - generalization: the filtration 𝓕_k = σ(U₀,…,U_{k−1}) → any filtration with W_k ∈ 𝓕_{k+1}; reason: the paper's filtration is an instance whenever the iterates are measurable
--   - encoding: measurability of the alignment events (implicit) → W_k is 𝓕_{k+1}-measurable; reason: without it P[W_k | 𝓕_k] is undefined
--   - reading: 𝓛_f(x₀) → 𝓛_F(x₀) = {y : F(y) ≤ F(x₀)}; reason: the only sublevel set the paper defines (p.7); (18) and the proof of Lemma 5 use conv(𝓛_F(x₀)); boundedness of {f ≤ f(x₀)} would not make H_{F,U} finite
--   - encoding: H_{F,U_k} ≤ H_{F,max}, with H_{F,U_k} the max in (18) → IsCurvBound: ‖U_kᵀ∇̄²Ψ(z)U_k + H_{f,U_k}I‖_F ≤ Hmax for all z₁,…,zₙ ∈ conv 𝓛_F(x₀); reason: a max is ≤ B iff every value is ≤ B; avoids a real sSup
--   - encoding: P[min_{0≤i≤K} ‖∇F(x_i)‖² ≤ b] ≥ 1 − e^{…} → P[∀ i ≤ K, b < ‖∇F(x_i)‖²] ≤ e^{…}; reason: the same for measurable events; with the outer measure the bad-event form is the stronger
--   - generalization: f is L_U smooth along U (A.1) → f differentiable on ℝⁿ and (2) for U with constant L_U; reason: the paper defines the term by (2) and uses nothing else; any smooth f satisfying (2) is an instance
--   - encoding: ψ is simple (A.2) → not stated; reason: a computational remark (the prox of ψ along U is cheap), not a mathematical condition
--   - encoding: A.3: a solution of (1) exists, F* = min F → a point x* with F(x*) ≤ F(y) for all y; F* written F(x*); reason: the same hypothesis; F* is the value at a minimizer
--   - encoding: vectors of ℝⁿ, ℝᵖ and matrices U ∈ ℝ^{n×p} → EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin p), U acting through Matrix.toEuclideanLin; reason: Lean convention; the Euclidean norm and inner product of the paper, same instances
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Theorem 1, display (22), p.10

import Mathlib
import Definitions.Def_StochCoordProx_IsSmoothAlong
import Definitions.Def_StochCoordProx_IsSCPGRun
import Definitions.Def_StochCoordProx_WellAligned
import Definitions.Def_StochCoordProx_IsCurvBound
import Definitions.Def_StochCoordProx_Assumption2

open MeasureTheory

namespace StochCoordProx

/-- **Theorem 1 (high-probability sublinear rate of SCPG, nonconvex case).** Let
`F = f + ψ` on `ℝⁿ` satisfy Assumption 1 (`f` differentiable and `L_U` smooth along every
`U ∈ 𝒰`; `ψ` twice continuously differentiable; a minimizer `x*`, `F* = F(x*)`), and let the
sublevel set `𝓛_F(x₀)` be bounded. Let `α, δ ∈ (0,1)`, and let `(U_k, η_k, x_k, d_k)` be an
SCPG run from `x₀` on a probability space `(Ω, P)` with filtration `𝓕` satisfying Assumption 2
for the alignment events `{U_k is well-aligned at x_k}`. Let `η_min, H_{F,max} > 0` with
`η_min ≤ η_{U_k}` and `H_{F,U_k} ≤ H_{F,max}` for all `k` (21), and `C = α² η_min / (2 H²_{F,max})`.
Then for all `β ∈ (0,1)` and `K ≥ 0`
`P[min_{0≤i≤K} ‖∇F(xᵢ)‖² ≤ (F(x₀) − F*)/(C(1−β)(1−δ)(K+1))] ≥ 1 − e^{−(β²/2)(1−δ)(K+1)}`  (22),
stated as the bound `≤ e^{−(β²/2)(1−δ)(K+1)}` on the probability of the complementary event
`∀ i ≤ K, ‖∇F(xᵢ)‖² > (F(x₀) − F*)/(C(1−β)(1−δ)(K+1))`.

Necoara & Chorobura, arXiv:2104.13370v3, Theorem 1, display (22), p.10.

**Formalization Note.**
* `ℝⁿ`, `ℝᵖ` are `EuclideanSpace ℝ (Fin n)`, `EuclideanSpace ℝ (Fin p)`; matrices act through
  `Matrix.toEuclideanLin`; `‖·‖_F` in (18) is the Frobenius norm written out.
* The run is pathwise (`x k ω`, …); `η_min`, `H_{F,max}` and hence `C` are functions of `ω`
  (constant bounds and the pathwise `min_k η_{U_k}` are special cases); their positivity only
  excludes the cases where `C` is undefined.
* Assumption 2 is the conditional probability `P⟦W k | 𝓕 k⟧ ≥ 1 − δ` a.s., with `W k` adapted.
* The paper's "𝓛_f(x₀)" is read as `𝓛_F(x₀) = {F ≤ F(x₀)}`; boundedness of `𝒰` is not assumed.
* "min ≤ b" is negated to "`∀ i ≤ K`, `b < ‖∇F(xᵢ)‖²`" (bad-event form), whose measure is bounded
  from above. -/
theorem theorem_1_high_prob_rate {n p : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℕ m0)
    (f ψ : EuclideanSpace ℝ (Fin n) → ℝ) (𝒰 : Set (Matrix (Fin n) (Fin p) ℝ))
    (L : Matrix (Fin n) (Fin p) ℝ → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hf : Differentiable ℝ f) (hL : ∀ V ∈ 𝒰, IsSmoothAlong f V (L V)) (hψ : ContDiff ℝ 2 ψ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : ∀ y, f xstar + ψ xstar ≤ f y + ψ y)
    (hbdd : Bornology.IsBounded {y : EuclideanSpace ℝ (Fin n) | f y + ψ y ≤ f x₀ + ψ x₀})
    (α δ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (U : ℕ → Ω → Matrix (Fin n) (Fin p) ℝ) (η : ℕ → Ω → ℝ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (d : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsSCPGRun f ψ 𝒰 L x₀ U η x d)
    (hA2 : Assumption2 P 𝓕
      (fun k => {ω : Ω | WellAligned α (gradient (fun y => f y + ψ y) (x k ω)) (U k ω)}) δ)
    (ηmin Hmax : Ω → ℝ) (hηmin_pos : ∀ ω, 0 < ηmin ω) (hηmin : ∀ ω k, ηmin ω ≤ η k ω)
    (hHmax_pos : ∀ ω, 0 < Hmax ω)
    (hHmax : ∀ ω k, IsCurvBound f ψ x₀ (U k ω) (Hf ψ 𝒰 (L (U k ω)) (η k ω)) (Hmax ω))
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (K : ℕ) :
    P {ω : Ω | ∀ i ≤ K,
        ((f x₀ + ψ x₀) - (f xstar + ψ xstar)) /
            (α ^ 2 * ηmin ω / (2 * Hmax ω ^ 2) * (1 - β) * (1 - δ) * (K + 1)) <
          ‖gradient (fun y => f y + ψ y) (x i ω)‖ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-(β ^ 2 / 2) * (1 - δ) * (K + 1))) := by sorry

end StochCoordProx
