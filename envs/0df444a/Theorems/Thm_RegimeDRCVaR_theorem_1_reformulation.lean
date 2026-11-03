-- Prove2me | Theorems.Thm_RegimeDRCVaR_theorem_1_reformulation
-- name    : RegimeDRCVaR.theorem_1_reformulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:20.398161+00:00
-- url     : https://prove2.me/theorems/0bf5b3e4-d1c2-4834-8c7e-6a5f635f307a
-- title:
--   Theorem 1 — for every $m\in[1,+\infty]$ the worst-case CVaR problem (11) is the convex program (12) (corrected: regime budget of (9))
-- statement:
--   Let $K$ regimes have return samples $r_{nk}\in\mathbb R^I$ ($n\in[N_k]$, $N_k\ge1$), regime probabilities $w_k\ge0$ with $\sum_kw_k=1$, and radii $\theta_k\ge0$; let $\eta\in(0,1)$, $m\in[1,+\infty]$ and $\mathcal X=\{x\mid Ax=b,\ Cx\ge d\}$. Problem (11) is
--   $$
--   \min_{x\in\mathcal X,\,v\in\mathbb R}\Big\{v+\frac1{1-\eta}\sup_{\mathbb P\in\mathcal U_{rs}(\boldsymbol\theta)}\mathbb E^{\mathbb P}[G(x,\tilde r)]\Big\},
--   $$
--   with $\rho$ the $\ell_m$ norm in $\mathcal U_{rs}(\boldsymbol\theta)$, and problem (12) is
--   $$
--   \begin{aligned}
--   \min_{v,x,\boldsymbol\alpha,\beta}\ & v+\frac1{1-\eta}\Big[\sum_{k\in[K]}\sum_{n\in[N_k]}\frac{w_k}{N_k}\alpha_{nk}+\beta\sum_{k\in[K]}w_k\theta_k\Big]\\
--   \text{s.t. }& r_{nk}'x\ge-\alpha_{nk}-v,\quad \beta\ge\|x\|_{m^*},\quad \alpha_{nk}\ge0\quad(\forall n\in[N_k],k\in[K]),\quad x\in\mathcal X.
--   \end{aligned}
--   $$
--   Then (11) can be reformulated as (12):
--
--   1. for every $x\in\mathcal X$ and $v\in\mathbb R$, the objective of (11) at $(x,v)$ is the minimum of the objective of (12) over the $(\boldsymbol\alpha,\beta)$ that make $(v,x,\boldsymbol\alpha,\beta)$ feasible for (12) (a lower bound, attained);
--   2. the optimal values of (11) and (12) are equal;
--   3. $(x,v)$ is optimal for (11) iff $(v,x,\boldsymbol\alpha,\beta)$ is optimal for (12) for some $(\boldsymbol\alpha,\beta)$;
--   4. for $m=1$ (and $I\ge1$ assets) the constraint $\beta\ge\|x\|_{m^*}$ is the linear system $\beta\ge\pm x_i$ ($i\in[I]$), and for $m=2$ it is the second-order cone constraint $\|x\|_2\le\beta$; so (12) is a linear program for $m=1$ and a second-order cone program for $m=2$.
--
--   The distributionally robust CVaR portfolio problem over the regime-switching ambiguity set is thus a finite convex program of the size of the data, solvable by standard LP/SOCP software for the two most common norms.
--
--   **Formalization Note** Objectives of (11) and optimal values are extended reals; both optimal values are $+\infty$ when $\mathcal X$ is empty.
--
--   Differences from the source:
--   - correction: display (9): 𝔼^P[ũ_k] ≤ θ_k for every k → Urs: 𝔼^P[ũ_k 1{k̃ = k}] ≤ w_kθ_k for every k; reason: the printed budget leaves ũ_k (k ≠ k̃) free and makes Theorem 1 false: K = 2, w = (½, ½), N₁ = N₂ = 1, I = 1, r₁₁ = r₁₂ = 0, θ = (1, 1); r̃ = −M, ũ = (M, 0) on k̃ = 1 and r̃ = 0, ũ = (−M, 0) on k̃ = 2 satisfy (9) for every M, so (11) = +∞ while (12) is finite; the corrected budget is the proof's own first display (p.ec2) and (EC.1)
--   - encoding: P[ñ = n | k̃ = k] = 1/N_k and P[k̃ = k] = w_k on ℝ^I × ℝ^K × [N_k]_{k=1}^K × [K] → P[k̃ = k, ñ = n] = w_k/N_k and P[k̃ = k] = w_k on (Fin I → ℝ) × (Fin K → ℝ) × (Fin K × ℕ); support ‖r̃ − r_{ñk̃}‖_m ≤ ũ_{k̃} a.s.; reason: the same laws (the joint masses sum to one, so ñ < N_{k̃} a.s.); the joint form is defined when w_k = 0
--   - encoding: standing assumptions of §3 (m ∈ [1,+∞], η ∈ (0,1), N_k sample counts, w_k regime probabilities, θ_k radii) → hypotheses 1 ≤ m, 0 < η < 1, 0 < N k, 0 ≤ w k, ∑ w = 1, 0 ≤ θ k; reason: the paper's setting, made explicit; no other hypothesis is added
--   - encoding: ℓm norm ‖·‖_m and conjugate norm ‖·‖_{m*} on ℝ^I → normM m (the PiLp m norm on Fin I → ℝ) and normM (ENNReal.conjExponent m); reason: Lean convention; ENNReal.conjExponent sends 1 ↦ ∞, 2 ↦ 2, ∞ ↦ 1, the Hölder conjugate
--   - encoding: sup and min of real-valued problems → worst case as an ℝ≥0∞ supremum of lower integrals; objectives of (11) and optimal values as EReal infima; reason: Lean convention; the loss is nonnegative and the values are finite on every instance where the source's are, ±∞ otherwise
--   - encoding: regimes k ∈ [K], scenarios n ∈ [N_k], samples r_nk → k : Fin K, n : Fin (N k), r k n; reason: Lean convention; index i − 1 for paper index i
--   - reading: (11) can be reformulated as (12) → clauses 1–3: pointwise identity with attainment over (α, β), equal optimal values, and correspondence of optimal solutions; reason: the strong reading of 'reformulated', which the proof establishes; equality of values alone would be weaker
--   - encoding: when m = 1 and m = 2, (12) is a linear program and second-order conic program → clause 4: m = 1 → 0 < I → (β ≥ ‖x‖_{m*} ↔ ∀ i, β ≥ x i ∧ β ≥ −x i); m = 2 → (β ≥ ‖x‖_{m*} ↔ (x, β) ∈ LorentzCone I); reason: the other constraints of (12) and 𝒳 are affine, so this is what makes (12) an LP or an SOCP; 'tractable' is not a mathematical claim
--   - reading: a market with I risky assets, i ∈ [I] (p.9) → the m = 1 clause assumes 0 < I; reason: the source has I ≥ 1 assets (its budget 1′x = 1 needs one); for I = 0, ‖x‖_∞ = 0 and the system β ≥ ±x_i is empty, so the equivalence would fail at β = −1; no other clause carries the hypothesis
--   - generalization: 𝒳 = {x | Ax = b, Cx ≥ d} with the budget constraint 1′x = 1 embedded in it as a necessary constraint (p.9) → feasX A b C d for arbitrary A, b, C, d (no budget row required); reason: the argument never uses the budget row; the source’s 𝒳 is the instance in which one row of (A, b) is (1′, 1)
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, Theorem 1, displays (11)–(12), p.13; proof pp.ec2–ec3

import Mathlib
import Definitions.Def_RegimeDRCVaR_val11
import Definitions.Def_RegimeDRCVaR_val12
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone

open scoped ENNReal

namespace RegimeDRCVaR

/-- **Theorem 1** (Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, p.13): "∀m ∈ [1,+∞],
the problem (11) under the ambiguity set U_rs(θ) in (9) with ρ(·,·) defined by ℓm-norm can be
reformulated as: min_{v,x,α,β} v + 1/(1−η) [∑_{k∈[K]} ∑_{n∈[N_k]} (w_k/N_k) α_{nk} +
β ∑_{k∈[K]} w_kθ_k] s.t. r′_{nk}x ≥ −α_{nk} − v, β ≥ ‖x‖_{m*}, α_{nk} ≥ 0, x ∈ 𝒳 (12). In
particular, when m = 1 and m = 2, (12) is a linear program and second-order conic program,
respectively, which are both tractable."

Four clauses:
1. (pointwise, with attainment) for every `x ∈ 𝒳` and `v ∈ ℝ`, the objective of (11) at `(x, v)` is
   the minimum of the objective of (12) over the `(α, β)` that make `(v, x, α, β)` feasible for
   (12): it is a lower bound for all of them and is attained by one;
2. (values) the optimal values of (11) and (12) are equal;
3. (solutions) `(x, v)` is optimal for (11) iff `(v, x, α, β)` is optimal for (12) for some `(α, β)`;
4. (tractable forms) for `m = 1` (and `I ≥ 1` assets) the constraint `β ≥ ‖x‖_{m*}` is the
   linear system `β ≥ ±x_i`, and for `m = 2` it is the second-order cone constraint `‖x‖₂ ≤ β`.

**Formalization Note**
* `U_rs(θ)` carries the corrected regime budget `𝔼^P[ũ_k 1{k̃ = k}] ≤ w_kθ_k` (see `Urs`); with
  the printed `𝔼^P[ũ_k] ≤ θ_k` the theorem is false.
* Standing assumptions of §3: `m ∈ [1, ∞]`, `η ∈ (0, 1)`, `N_k ≥ 1`, `w` a probability vector
  (so `K ≥ 1`), `θ_k ≥ 0`; `𝒳 = {x | Ax = b, Cx ≥ d}` is an arbitrary polyhedron (possibly empty).
* Objectives of (11) and optimal values are in `EReal`; the objective of (12) is real.
* The `m = 1` clause assumes `0 < I` (p.9: "a market with I risky assets", whose budget
  `1′x = 1` needs `I ≥ 1`): for `I = 0` the norm is `0` and the system `β ≥ ±x_i` is empty, so the
  equivalence would fail at `β = −1`. No other clause needs it.
* `𝒳 = {x | Ax = b, Cx ≥ d}` is any polyhedron; the paper embeds the budget row `1′x = 1` in it,
  which is the special case where one row of `A`, `b` is `1′`, `1`.
* "is a linear program / second-order conic program" is formalized as clause 4: with the affine
  constraints of (12) and polyhedral `𝒳`, it is what makes (12) an LP (`m = 1`) or an SOCP
  (`m = 2`). -/
theorem theorem_1_reformulation {I K p q : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞) (hm : 1 ≤ m)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (w θ : Fin K → ℝ) (η : ℝ)
    (hN : ∀ k, 0 < N k) (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (hθ : ∀ k, 0 ≤ θ k)
    (hη0 : 0 < η) (hη1 : η < 1)
    (A : Matrix (Fin p) (Fin I) ℝ) (b : Fin p → ℝ) (C : Matrix (Fin q) (Fin I) ℝ)
    (d : Fin q → ℝ) :
    (∀ x ∈ feasX A b C d, ∀ v : ℝ,
      (∀ (α : (k : Fin K) → Fin (N k) → ℝ) (β : ℝ), feas12 m r A b C d v x α β →
        obj11 m r w θ η x v ≤ ((obj12 w θ η v α β : ℝ) : EReal)) ∧
      ∃ (α : (k : Fin K) → Fin (N k) → ℝ) (β : ℝ), feas12 m r A b C d v x α β ∧
        obj11 m r w θ η x v = ((obj12 w θ η v α β : ℝ) : EReal)) ∧
    val11 m r w θ η A b C d = val12 m r w θ η A b C d ∧
    (∀ (x : Fin I → ℝ) (v : ℝ),
      (x ∈ feasX A b C d ∧
          ∀ x' ∈ feasX A b C d, ∀ v' : ℝ, obj11 m r w θ η x v ≤ obj11 m r w θ η x' v') ↔
        ∃ (α : (k : Fin K) → Fin (N k) → ℝ) (β : ℝ), feas12 m r A b C d v x α β ∧
          ∀ (v' : ℝ) (x' : Fin I → ℝ) (α' : (k : Fin K) → Fin (N k) → ℝ) (β' : ℝ),
            feas12 m r A b C d v' x' α' β' → obj12 w θ η v α β ≤ obj12 w θ η v' α' β') ∧
    (m = 1 → 0 < I → ∀ (x : Fin I → ℝ) (β : ℝ),
      β ≥ normM (ENNReal.conjExponent m) x ↔ ∀ i, β ≥ x i ∧ β ≥ -x i) ∧
    (m = 2 → ∀ (x : Fin I → ℝ) (β : ℝ),
      β ≥ normM (ENNReal.conjExponent m) x ↔ (x, β) ∈ PolyhedralSOC.Shared.LorentzCone I) := by sorry

end RegimeDRCVaR
