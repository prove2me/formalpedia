-- Prove2me | Theorems.Thm_StochCoordProx_display_23_telescoping
-- name    : StochCoordProx.display_23_telescoping
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:35:00.262104+00:00
-- url     : https://prove2.me/theorems/3c1af431-a905-41fc-adea-4bdc13aaddd2
-- title:
--   (23) — $\frac{\eta_{\min}}2\sum_{i=0}^K\|d_i\|^2\le F(x_0)-F^*$
-- statement:
--   Let $F=f+\psi$ with $f$ differentiable and $L_U$ smooth along every $U\in\mathcal U$, and let $x^*$ minimize $F$, $F^*=F(x^*)$. Let $(U_k,\eta_k,x_k,d_k)$ be a run of SCPG from $x_0$, fix an outcome $\omega$, let $\eta_{\min}\le\eta_{U_k}$ for all $k$, and let $K\ge0$. Then
--
--   $$
--   \frac{\eta_{\min}}{2}\sum_{i=0}^K\|d_i\|^2\le\sum_{i=0}^K\frac{\eta_{U_i}}{2}\|d_i\|^2\le\sum_{i=0}^K\bigl(F(x_i)-F(x_{i+1})\bigr)=F(x_0)-F(x_{K+1})\le F(x_0)-F^* .
--   $$
--
--   Summing the descent inequality of Lemma 4 bounds the total squared step length by the initial optimality gap.
--
--   Differences from the source:
--   - generalization: η_min = min_{k∈ℕ} η_{U_k} (21) → any ηmin(ω) with ηmin(ω) ≤ η_k(ω) for all k; reason: (23) uses only η_min ≤ η_{U_i}; the paper's η_min is an instance
--   - generalization: Assumption 1 (including ψ C² and simple) → f differentiable, (2) for every U ∈ 𝒰, a minimizer x*; no regularity of ψ; reason: the chain uses Lemma 4, which needs no regularity of ψ, and F* = F(x*)
--   - generalization: η_{U_k} > 0 chosen as a function of U_k → η_k(ω) > 0, any positive choice at step k on outcome ω; reason: Algorithm 1 leaves the choice to the user; a choice depending only on U_k is an instance
--   - generalization: U_k ∼ 𝒰 randomly sampled from a distribution on 𝒰 → any U_k(ω) ∈ 𝒰 on each outcome ω, no distribution fixed; reason: the randomness enters the analysis only through Assumption 2, which is a hypothesis where it is used
--   - generalization: f is L_U smooth along U (A.1) → f differentiable on ℝⁿ and (2) for U with constant L_U; reason: the paper defines the term by (2) and uses nothing else; any smooth f satisfying (2) is an instance
--   - encoding: A.3: a solution of (1) exists, F* = min F → a point x* with F(x*) ≤ F(y) for all y; F* written F(x*); reason: the same hypothesis; F* is the value at a minimizer
--   - encoding: the displayed chain of relations → the conjunction of its four links; reason: the same content
--   - encoding: vectors of ℝⁿ, ℝᵖ and matrices U ∈ ℝ^{n×p} → EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin p), U acting through Matrix.toEuclideanLin; reason: Lean convention; the Euclidean norm and inner product of the paper, same instances
--   - generalization: the set 𝒰 bounded (standing assumption, p.4); 𝓛_F(x₀) bounded (standing assumption, p.7: "Throughout the paper, we also assume boundedness of the level set") → not assumed; reason: the proof does not use them; they serve only to make H_{F,max} finite, which this statement does not involve; every instance satisfying them is covered
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, proof of Theorem 1, display (23), p.11

import Mathlib
import Definitions.Def_StochCoordProx_IsSmoothAlong
import Definitions.Def_StochCoordProx_IsSCPGRun

namespace StochCoordProx

/-- **Display (23)** (proof of Theorem 1): for an SCPG run from `x₀` (Assumption 1: `f`
differentiable and `L_U` smooth along every `U ∈ 𝒰`, and a minimizer `x*` of `F = f + ψ`, so
`F* = F(x*)`), every outcome `ω`, every lower bound `η_min ≤ η_{U_k}` (all `k`) and every
`K ≥ 0`,
`(η_min/2) ∑_{i=0}^K ‖dᵢ‖² ≤ ∑_{i=0}^K (η_{Uᵢ}/2) ‖dᵢ‖² ≤ ∑_{i=0}^K (F(xᵢ) − F(x_{i+1}))
  = F(x₀) − F(x_{K+1}) ≤ F(x₀) − F*`.

Necoara & Chorobura, arXiv:2104.13370v3, proof of Theorem 1, display (23), p.11.

**Formalization Note.** The chain is stated as the conjunction of its four links. The run is
pathwise (`x i ω`, `d i ω`, `η i ω`); `ηmin ω` is any lower bound of the `η k ω` on that
outcome, the paper's `η_min = min_k η_{U_k}` (21) being one. `∑_{i=0}^K` is
`∑ i ∈ Finset.range (K + 1)`. -/
theorem display_23_telescoping {n p : ℕ} {Ω : Type*} (f ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (𝒰 : Set (Matrix (Fin n) (Fin p) ℝ)) (L : Matrix (Fin n) (Fin p) ℝ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hf : Differentiable ℝ f)
    (hL : ∀ V ∈ 𝒰, IsSmoothAlong f V (L V)) (xstar : EuclideanSpace ℝ (Fin n))
    (hxstar : ∀ y, f xstar + ψ xstar ≤ f y + ψ y)
    (U : ℕ → Ω → Matrix (Fin n) (Fin p) ℝ) (η : ℕ → Ω → ℝ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (d : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsSCPGRun f ψ 𝒰 L x₀ U η x d) (ηmin : Ω → ℝ) (hηmin : ∀ ω k, ηmin ω ≤ η k ω)
    (ω : Ω) (K : ℕ) :
    ηmin ω / 2 * ∑ i ∈ Finset.range (K + 1), ‖d i ω‖ ^ 2 ≤
        ∑ i ∈ Finset.range (K + 1), η i ω / 2 * ‖d i ω‖ ^ 2 ∧
      ∑ i ∈ Finset.range (K + 1), η i ω / 2 * ‖d i ω‖ ^ 2 ≤
        ∑ i ∈ Finset.range (K + 1),
          ((f (x i ω) + ψ (x i ω)) - (f (x (i + 1) ω) + ψ (x (i + 1) ω))) ∧
      ∑ i ∈ Finset.range (K + 1),
          ((f (x i ω) + ψ (x i ω)) - (f (x (i + 1) ω) + ψ (x (i + 1) ω))) =
        (f x₀ + ψ x₀) - (f (x (K + 1) ω) + ψ (x (K + 1) ω)) ∧
      (f x₀ + ψ x₀) - (f (x (K + 1) ω) + ψ (x (K + 1) ω)) ≤
        (f x₀ + ψ x₀) - (f xstar + ψ xstar) := by sorry

end StochCoordProx
