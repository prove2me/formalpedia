-- Prove2me | Theorems.Thm_TimeInconsLQ_Sufficient_proposition_3_1
-- name    : TimeInconsLQ.Sufficient.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:28.847729+00:00
-- url     : https://prove2.me/theorems/0fa986e3-049c-4b3c-bed6-99fc5433eb62
-- title:
--   Proposition 3.1 — the second-order expansion (3.3) of the conditional cost under a spike variation
-- statement:
--   Assume the standing assumptions. Let $u^*$ be an admissible control with state $X^*$, let $t\in[0,T)$, and let $(p(\cdot;t),k(\cdot;t))$ and $(P(\cdot;t),K(\cdot;t))$ solve the adjoint equations (3.1) and (3.2) on $[t,T]$. Put
--
--   $$\Lambda(s;t)=B_sp(s;t)+\sum_{j=1}^d(D^j_s)'k^j(s;t)+R_su^*_s,\qquad H(s;t)=R_s+\sum_{j=1}^d(D^j_s)'P(s;t)D^j_s.$$
--
--   For $\varepsilon>0$ and $v\in L^2_{\mathcal F_t}(\Omega;\mathbb R^l)$ let $u^{t,\varepsilon,v}$ be the spike variation (2.4). Then
--
--   $$J(t,X^*_t;u^{t,\varepsilon,v})-J(t,X^*_t;u^*)=\mathbb E_t\int_t^{t+\varepsilon}\Big\{\langle\Lambda(s;t),v\rangle+\tfrac12\langle H(s;t)v,v\rangle\Big\}ds+o(\varepsilon).\qquad(3.3)$$
--
--   Here $o(\varepsilon)$ means: for every sequence $\varepsilon_k\downarrow0$ with $\varepsilon_k>0$ and every choice of states of the controls $u^{t,\varepsilon_k,v}$, almost surely the difference between the two sides, divided by $\varepsilon_k$, tends to $0$.
--
--   The expansion reduces the equilibrium condition of Definition 2.1 to properties of the adjoint processes; it is the main step towards Theorem 3.2.
--
--   **Formalization Note.** The paper's $o(\varepsilon)$ is a statement about conditional expectations, which are defined only up to null sets, at uncountably many $\varepsilon$; it is read version-robustly along sequences, almost surely for each sequence, as in Definition 2.1. $J$ is the conditional cost of the model; $x_t=X^*_t$ in both terms. The integral $\int_t^{t+\varepsilon}$ is over $[t,t+\varepsilon]$; only small $\varepsilon$ (with $t+\varepsilon<T$) matter for the limit.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 5, Proposition 3.1, (3.3)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Sufficient_Model
import Definitions.Def_TimeInconsLQ_Sufficient_Adjoint

namespace TimeInconsLQ.Sufficient

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- Proposition 3.1, p. 5: the second-order expansion (3.3). Let `u*` be admissible with state
`X*`, `t ∈ [0, T)`, `(p, k)` a solution of (3.1) and `(P, K)` a solution of (3.2) on `[t, T]`,
and `v ∈ L²_{𝓕ₜ}(Ω; ℝˡ)`. Then
`J(t, X*_t; u^{t,ε,v}) − J(t, X*_t; u*) = E_t ∫ₜ^{t+ε} {⟨Λ(s;t), v⟩ + ½⟨H(s;t) v, v⟩} ds + o(ε)`,
where the remainder is `o(ε)` in the sense: along every sequence `εₖ ↓ 0`, for every choice of
states of the perturbed controls, almost surely the remainder divided by `εₖ` tends to `0`. -/
theorem proposition_3_1 {Ω : Type*} [MeasurableSpace Ω] {n l d : ℕ} (M : Data Ω n l d)
    (hM : Standing M) (u : ℝ≥0 → Ω → Fin l → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ)
    (hu : Admissible M u) (hX : IsState M u X) (t : ℝ≥0) (ht : t < M.T)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (k : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (hp : FirstAdjoint M X t p k)
    (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (K : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hP : SecondAdjoint M t Pm K)
    (v : Ω → Fin l → ℝ) (hv : StronglyMeasurable[filt M t] v)
    (hv2 : ∫⁻ ω, ‖v ω‖ₑ ^ 2 ∂M.P < ⊤)
    (εs : ℕ → ℝ) (hε : ∀ m, 0 < εs m) (hε0 : Tendsto εs atTop (𝓝 0))
    (Xε : ℕ → ℝ≥0 → Ω → Fin n → ℝ) (hXε : ∀ m, IsState M (spike u t (εs m) v) (Xε m)) :
    ∀ᵐ ω ∂M.P, Tendsto (fun m =>
      (cost M t (X t) (spike u t (εs m) v) (Xε m) ω - cost M t (X t) u X ω
        - condExp (filt M t) M.P (fun ω' => ∫ s in Set.Icc (t : ℝ) ((t : ℝ) + εs m),
            (Lam M u p k s.toNNReal ω' ⬝ᵥ v ω'
              + (1 / 2 : ℝ) * ((Hmat M Pm s.toNNReal ω' *ᵥ v ω') ⬝ᵥ v ω'))) ω)
        / εs m) atTop (𝓝 0) := by sorry

end TimeInconsLQ.Sufficient
