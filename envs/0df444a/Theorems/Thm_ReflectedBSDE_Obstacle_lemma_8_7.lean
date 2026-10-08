-- Prove2me | Theorems.Thm_ReflectedBSDE_Obstacle_lemma_8_7
-- name    : ReflectedBSDE.Obstacle.lemma_8_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:20.717116+00:00
-- url     : https://prove2.me/theorems/96ab324d-5692-470d-974d-a3354384d222
-- title:
--   Lemma 8.7 — properties of doubled-variable maximizers
-- statement:
--   Let $u$ and $v_0$ be continuous on a closed time strip and ball, and let $v(t,x)=v_0(t,x)+\varepsilon/t$ for $t>0$. Suppose the terminal values obey $u(T,x)\le v_0(T,x)$, while at an interior point $(t_0,x_0)$ the gap $\delta=u(t_0,x_0)-v(t_0,x_0)>0$ exceeds every positive boundary gap. For each $\alpha>0$, choose any maximizer $(\hat t_\alpha,\hat x_\alpha,\hat y_\alpha)$ of $\Phi_\alpha$ over positive times and the closed ball. Then
--
--   $$
--   \begin{aligned}
--   &(\hat t_\alpha,\hat x_\alpha,\hat y_\alpha)\in(0,T)\times B_R\times B_R\quad\text{for all sufficiently large }\alpha,\\
--   &\alpha|\hat x_\alpha-\hat y_\alpha|^2\to0,\qquad |\hat x_\alpha-\hat y_\alpha|^2\to0,\\
--   &u(\hat t_\alpha,\hat x_\alpha)\ge v(\hat t_\alpha,\hat y_\alpha)+\delta\quad\text{for every }\alpha>0.
--   \end{aligned}
--   $$
--
--   This lemma controls the maximizers used in the comparison argument.
--
--   **Formalization Note** The paper's $v$ includes the singular perturbation $\varepsilon/t$. Maximization is stated over $t>0$, where that expression is defined; the paper's boundary convention at $t=0$ is its limit $+\infty$. The ball $B_R=\{x:|x|<R\}$ and its closure are Euclidean, written $\sum_i x_i^2<R^2$ and $\sum_i x_i^2\le R^2$. The terminal hypothesis is the inequality $u(T,x)\le v_0(T,x)$, which the paper's equality $u(T,\cdot)=g=v(T,\cdot)-\varepsilon/T$ implies and which suffices for its proof.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 733, Lemma 8.7 (proof pp. 734–735)

import Definitions.Def_ReflectedBSDE_Obstacle_penalty

open Filter Topology
open scoped NNReal

namespace ReflectedBSDE.Obstacle

/-- Lemma 8.7, for the bounded transformed functions used in the comparison
proof. The ball `B_R = {x ; |x| < R}` is Euclidean, written
`∑ i, x i ^ 2 < R ^ 2`. The function `v₀` is the transformed supersolution
before adding ε/t; `v` is its singular perturbation on positive times. -/
theorem lemma_8_7 {d : ℕ} (T : ℝ≥0) (hT : 0 < T)
    (R ε δ : ℝ) (hR : 0 < R) (hε : 0 < ε) (hδ : 0 < δ)
    (u v₀ v : ℝ≥0 → (Fin d → ℝ) → ℝ)
    (hu : ContinuousOn (fun z : ℝ≥0 × (Fin d → ℝ) => u z.1 z.2)
      (Set.Icc 0 T ×ˢ {x | ∑ i, x i ^ 2 ≤ R ^ 2}))
    (hv₀ : ContinuousOn (fun z : ℝ≥0 × (Fin d → ℝ) => v₀ z.1 z.2)
      (Set.Icc 0 T ×ˢ {x | ∑ i, x i ^ 2 ≤ R ^ 2}))
    (hv : ∀ t : ℝ≥0, 0 < t → t ≤ T → ∀ x, ∑ i, x i ^ 2 ≤ R ^ 2 →
      v t x = v₀ t x + ε / (t : ℝ))
    (hterminal : ∀ x, ∑ i, x i ^ 2 ≤ R ^ 2 → u T x ≤ v₀ T x)
    (t₀ : ℝ≥0) (x₀ : Fin d → ℝ)
    (ht₀ : 0 < t₀ ∧ t₀ ≤ T) (hx₀ : ∑ i, x₀ i ^ 2 < R ^ 2)
    (hdelta : δ = u t₀ x₀ - v t₀ x₀)
    (hboundary : ∀ t : ℝ≥0, 0 < t → t ≤ T →
      ∀ x : Fin d → ℝ, ∑ i, x i ^ 2 = R ^ 2 → max (u t x - v t x) 0 < δ)
    (hat : ℝ → ℝ≥0 × ((Fin d → ℝ) × (Fin d → ℝ)))
    (hhat : ∀ α : ℝ, 0 < α →
      0 < (hat α).1 ∧ (hat α).1 ≤ T ∧
      ∑ i, (hat α).2.1 i ^ 2 ≤ R ^ 2 ∧ ∑ i, (hat α).2.2 i ^ 2 ≤ R ^ 2)
    (hmax : ∀ α : ℝ, 0 < α →
      ∀ t : ℝ≥0, 0 < t → t ≤ T →
      ∀ x y : Fin d → ℝ, ∑ i, x i ^ 2 ≤ R ^ 2 → ∑ i, y i ^ 2 ≤ R ^ 2 →
      penalty u v α t x y ≤
        penalty u v α (hat α).1 (hat α).2.1 (hat α).2.2) :
    (∀ᶠ α : ℝ in atTop,
      (hat α).1 < T ∧ ∑ i, (hat α).2.1 i ^ 2 < R ^ 2 ∧
        ∑ i, (hat α).2.2 i ^ 2 < R ^ 2) ∧
    Tendsto (fun α : ℝ =>
      α * ∑ i, ((hat α).2.1 i - (hat α).2.2 i) ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun α : ℝ =>
      ∑ i, ((hat α).2.1 i - (hat α).2.2 i) ^ 2) atTop (𝓝 0) ∧
    ∀ α : ℝ, 0 < α →
      u (hat α).1 (hat α).2.1 ≥ v (hat α).1 (hat α).2.2 + δ := by sorry

end ReflectedBSDE.Obstacle
