-- Prove2me | Theorems.Thm_TSDRiem_theorem_4_5
-- name    : TSDRiem.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:30:52.457166+00:00
-- url     : https://prove2.me/theorems/c26ac4a6-0ad3-404b-abaf-523a8891c44b
-- title:
--   Theorem 4.5 — gradients vanish, limit points are stationary, g-convex gap is $O(1/t)$ (corrected: $\sqrt m\,\gamma<1$)
-- statement:
--   **Theorem 4.5 (Convergence with Deterministic $\mathcal P$), corrected.** Let $\nabla f$ be $L_f$-smooth and let $f^*=\min_{x\in M}f(x)$ be attained. Consider a run $\{x^t\}$ of Algorithm 1 with $m\ge1$ inner steps along which Assumption 4.1 holds with constants $L_1,\dots,L_m$, the stepsizes are $\eta_{t,k}=1/L_k$, and the selection is $(\gamma,r)$-gap ensuring (Assumption 4.2) with $\sqrt m\,\gamma<1$. Let
--
--   $$
--   \eta:=\frac{L_{\min}^2(1-\sqrt m\,\gamma)^2}{4L_{\max}\big(L_{\min}^2+L_f^2(m-1)m\big)},\qquad \eta':=\frac{L_{\min}r^2}{2m},\qquad A:=f(x^1)-f^*.
--   $$
--
--   Then:
--
--   1. $\lim_{t\to\infty}\|\nabla f(x^t)\|_{x^t}=0$, and for every integer $t>A/\eta'$
--   $$
--   \min_{s\in[t]}\|\nabla f(x^s)\|_{x^s}\le\max_{k\in\mathbb Z,\ 0\le k\le A/\eta'}\sqrt{\frac{A-\eta' k}{\eta\,(t-k)}} ,
--   $$
--   where the right-hand side is $O(m/\sqrt t)$: for every integer $t>A/\eta'$ it is at most $K_1\,m/\sqrt t$;
--   2. every limit point $x^*$ of $\{x^t\}$ is stationary: $\nabla f(x^*)=0$;
--   3. if in addition $f$ is geodesically convex and any two points of the sublevel set $\{x\in M: f(x)\le f(x^1)\}$ are at distance at most $R$, then for every $t\ge0$
--   $$
--   f(x^{t+1})-f^*\le\frac{A}{1+\min\Big\{\dfrac{A\,\eta}{R^2},\dfrac{\eta'}{A}\Big\}\,t} ,
--   $$
--   where the right-hand side is $O(m^2/t)$: for every integer $t\ge1$ it is at most $K_2\,m^2/t$.
--
--   The constants, which contain $t$ nowhere and $m$ only through $\sqrt m\,\gamma$, are
--
--   $$
--   K_1:=\frac{\sqrt{4A\,L_{\max}(L_{\min}^2+L_f^2)}}{L_{\min}(1-\sqrt m\,\gamma)},\qquad
--   K_2:=\max\Big\{\frac{4R^2L_{\max}(L_{\min}^2+L_f^2)}{L_{\min}^2(1-\sqrt m\,\gamma)^2},\ \frac{2A^2}{L_{\min}r^2}\Big\}.
--   $$
--
--   This is the deterministic convergence theorem for tangent subspace descent: under block smoothness and a gap ensuring selection rule, the method finds stationary points at the rate $O(1/\sqrt t)$ in gradient norm, and for geodesically convex objectives the optimality gap decays as $O(1/t)$, the rates of Euclidean block coordinate descent up to constants.
--
--   **Formalization Note** `x 1` is $x^1$, the iterate after the first outer iteration, and `x 0` is the initial point. The paper's "$=O(m/\sqrt t)$" and "$=O(m^2/t)$" are stated with the explicit constants $K_1,K_2$, which keeps the dependence on $m$; for fixed data they give `IsBigO` at `atTop` in $t$. A limit point is a cluster point (`MapClusterPt`) of $t\mapsto x^t$.
--
--   Differences from the source:
--   - correction: γ ∈ (0, 1] arbitrary → additionally √m·γ < 1; reason: the printed theorem is false. Counterexample: ℝ² with Exp_x(v) = x + v, f = ½‖x‖², m = 2, L_k = 1, stepsizes 1, γ = 1, any r > 0, x⁰ = (1, 0), both selected lines orthogonal to y^{t,0}; the iterates never move, every hypothesis holds (Assumption 4.2 with P′ = Π_{e₁}, Π_{e₂}), and ‖∇f(x^t)‖ = 1 for all t, contradicting parts 1–3; at √m·γ = 1 (γ = 1/√2, P′ the lines through (1, ±1)/√2) part 1 fails the same way
--   - generalization: a connected, geodesically complete Riemannian manifold with its Riemannian distance, exponential map, parallel transport and Riemannian gradient → an abstract metric space with finite-dimensional inner-product fibres, an exp map and isometric transports satisfying (A1) and (A2), and any function f with any gradient field; reason: Mathlib has no exponential map or parallel transport, and the paper's objects satisfy (A1), (A2) and isometry by the §2 facts (p.4)
--   - generalization: Assumptions 4.1 and 4.2 for the iterates of Algorithm 1 under a selection rule P → both assumptions along one given run whose subspaces are data; reason: every run of every rule satisfying them is such a run
--   - generalization: transport Γ^{y^{t,0}}_{y^{t,k−1}} along an unspecified geodesic → transport along the geodesic fixed by an arbitrary connecting vector w_{t,k}; reason: the statement holds for every choice
--   - generalization: "the diameter of {x ∈ M : f(x) ≤ f(x¹)} is R" → d(a, b) ≤ R for all a, b in the sublevel set; reason: the bound is monotone in R and the proof uses only d(x^s, x*) ≤ R, so the diameter itself is an instance
--   - reading: stepsize not printed in the theorem → η_{t,k} = 1/L_k; reason: the proof uses Lemma 4.4, which uses Lemma 4.1 with this stepsize, and the theorem is false for arbitrary stepsizes
--   - reading: L_max, L_min undefined in the paper → max_k L_k and min_k L_k; reason: the values the proofs of Lemmas 4.1 and 4.3 use
--   - reading: f* of problem (1) → f* ≤ f everywhere and f(z) = f* for some z; reason: (1) writes f* = min, and part 3's proof uses a minimizer x*
--   - reading: "For t > (f(x¹) − f*)/η′, we have lim_{t→∞} ‖∇f(x^t)‖ = 0" → the limit unconditionally; reason: a limit does not depend on t, and the proof of part 1 shows it outright
--   - reading: max over "k ≤ (f(x¹) − f*)/η′" → max over integers 0 ≤ k ≤ (f(x¹) − f*)/η′; reason: k counts the far-step iterations in the proof
--   - reading: "= O(m/√t)" and "= O(m²/t)" → the bounds are at most K₁·m/√t for every integer t > A/η′ and at most K₂·m²/t for every integer t ≥ 1, with explicit K₁, K₂ containing t nowhere and m only through √m·γ; reason: the paper does not say which quantities the O hides, and this is the stronger reading: it keeps m, hides L_f, L_min, L_max, r, R, A and 1 − √m·γ, and implies IsBigO at atTop in t for fixed data
--   - reading: "limit point x* ∈ M of {x^t}" → cluster point of the sequence t ↦ x^t (MapClusterPt); reason: standard meaning in a metric space
--   - encoding: m ∈ ℕ → 1 ≤ m; reason: at m = 0 the printed η′ = L_min r²/(2m) divides by zero
--   - encoding: quotients with f(x¹) = f* or R = 0 in part 3 → Lean's x/0 = 0; reason: these cases are undefined in the source; with x/0 = 0 the bound reads f(x^{t+1}) − f* ≤ 0 when f(x¹) = f* (true), and R = 0 forces f(x¹) = f*
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Theorem 4.5, p.14 (proof pp.14–15)

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting
import Definitions.Def_TSDRiem_RiemSetting_IsLSmooth
import Definitions.Def_TSDRiem_RiemSetting_IsGConvex
import Definitions.Def_TSDRiem_TSDRun
import Definitions.Def_TSDRiem_TSDRun_BlockSmooth
import Definitions.Def_TSDRiem_TSDRun_GapEnsuring
import Definitions.Def_TSDRiem_Lmax
import Definitions.Def_TSDRiem_Lmin
import Definitions.Def_TSDRiem_eta
import Definitions.Def_TSDRiem_etaPrime

open Filter Topology

namespace TSDRiem

/-- **Theorem 4.5 (Convergence with Deterministic P), corrected: `√m γ < 1`.** Let `f` be
`L_f`-smooth with `f∗ = min f`, let Assumption 4.1 hold (stepsizes `1/L_k`) and the rule be
`(γ, r)`-gap ensuring (Assumption 4.2), and let `{x^t}` be generated by Algorithm 1. With
`η := L²_min(1 − √m γ)² / (4L_max(L²_min + L²_f(m − 1)m))` and `η′ := L_min r²/(2m)`:
1. `lim_{t→∞} ‖∇f(x^t)‖ = 0`; for every integer `t > (f(x¹) − f∗)/η′`,
   `min_{s∈[t]} ‖∇f(x^s)‖ ≤ max_{k ≤ (f(x¹)−f∗)/η′} √((f(x¹) − f∗ − η′k)/(η(t − k)))`,
   and this bound is `O(m/√t)`: at most `K₁ m/√t` with `K₁` as below;
2. any limit point `x∗` of `{x^t}` is stationary, `∇f(x∗) = 0`;
3. if in addition `f` is g-convex and the sublevel set `{x : f(x) ≤ f(x¹)}` has diameter at most
   `R`, then for every `t`, `f(x^{t+1}) − f∗ ≤ (f(x¹) − f∗) /
   (1 + min{(f(x¹) − f∗)η/R², η′/(f(x¹) − f∗)} t)`, and this bound is `O(m²/t)`: at most
   `K₂ m²/t` for `t ≥ 1`, with `K₂` as below.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Theorem 4.5,
p.14.

Formalization Notes.
* Correction: `√m γ < 1` is added. Without it all three parts are false (ℝ², `f = ½‖x‖²`, `m = 2`,
  `L_k = 1`, `γ = 1`, `x⁰ = (1, 0)`, both selected lines orthogonal to `y^{t,0}`: the iterates
  never move, every hypothesis holds, and `‖∇f(x^t)‖ = 1`); at `√m γ = 1` part 1 fails the same
  way.
* Setting: the abstract `RiemSetting` (metric space, inner-product fibres, `exp`, isometric
  transports, axioms (A1), (A2) of p.4), with the gradient a field; the hypotheses of the rule are
  imposed along the run, whose connecting vectors are arbitrary (`TSDRun`).
* Readings: stepsizes `η_{t,k} = 1/L_k` (those of Lemma 4.1, used by the proof); `L_max`, `L_min`
  the max and min of the `L_k`; `f∗` attained (problem (1) is a `min`); the limit in part 1 holds
  unconditionally (it does not depend on `t`); `k` in the max ranges over the integers
  `0 ≤ k ≤ (f(x¹) − f∗)/η′`; "limit point" is a cluster point (`MapClusterPt`) of `t ↦ x^t`.
* "`= O(m/√t)`" and "`= O(m²/t)`": the paper's `O` hides the dependence on `L_f`, `L_min`, `L_max`,
  `r`, `R`, `f(x¹) − f∗` and `1 − √m γ` but keeps `m`, so the clauses are stated with explicit
  constants that contain `t` nowhere and `m` only through `√m γ`:
  `K₁ = √(4(f(x¹) − f∗) L_max (L²_min + L²_f)) / (L_min (1 − √m γ))` and
  `K₂ = max{4R²L_max(L²_min + L²_f)/(L²_min(1 − √m γ)²), 2(f(x¹) − f∗)²/(L_min r²)}`.
  They imply `IsBigO` at `atTop` in `t` with all data fixed.
* "The diameter of the sublevel set is `R`" is the pairwise bound `d(a, b) ≤ R` on the set
  (generalization). `x 1` is `x¹`, the iterate after the first outer iteration; `x 0` is `x⁰`.
* `1 ≤ m`: Algorithm 1 has at least one inner step; at `m = 0` the printed `η′ = L_min r²/(2m)`
  divides by zero.
* Lean's division by zero: if `R = 0` or `f(x¹) = f∗` a denominator in part 3 vanishes and the
  formula reads as Lean's `x / 0 = 0`; the statement is still the source's in those cases. -/
theorem theorem_4_5 {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    [∀ x, FiniteDimensional ℝ (T x)] (S : RiemSetting M T) (f : M → ℝ)
    (grad : (x : M) → T x) (Lf : ℝ) (hsmooth : S.IsLSmooth grad Lf)
    (fstar : ℝ) (hfstar : ∀ z, fstar ≤ f z) (hfstar_att : ∃ z, f z = fstar)
    {m : ℕ} (hm : 1 ≤ m) (R : TSDRun S grad m) (L : Fin m → ℝ) (h41 : R.BlockSmooth f L)
    (hstep : ∀ t, 1 ≤ t → ∀ k, R.η t k = 1 / L k) (γ r : ℝ) (h42 : R.GapEnsuring γ r)
    (hγ : Real.sqrt m * γ < 1) :
    let η := eta m L Lf γ
    let η' := etaPrime m L r
    let A := f (R.x 1) - fstar
    Tendsto (fun t => ‖grad (R.x t)‖) atTop (𝓝 0) ∧
    (∀ t : ℕ, A / η' < t →
      (⨅ s : Finset.Icc 1 t, ‖grad (R.x s)‖) ≤
        ⨆ k : Finset.range (⌊A / η'⌋₊ + 1),
          Real.sqrt ((A - η' * (k : ℕ)) / (η * ((t : ℝ) - (k : ℕ))))) ∧
    (∀ t : ℕ, A / η' < t →
      (⨆ k : Finset.range (⌊A / η'⌋₊ + 1),
        Real.sqrt ((A - η' * (k : ℕ)) / (η * ((t : ℝ) - (k : ℕ))))) ≤
      Real.sqrt (4 * A * Lmax L * (Lmin L ^ 2 + Lf ^ 2)) /
        (Lmin L * (1 - Real.sqrt m * γ)) * m / Real.sqrt t) ∧
    (∀ xs : M, MapClusterPt xs atTop R.x → grad xs = 0) ∧
    (S.IsGConvex f grad → ∀ Rd : ℝ,
      (∀ a b, f a ≤ f (R.x 1) → f b ≤ f (R.x 1) → dist a b ≤ Rd) →
      (∀ t : ℕ, f (R.x (t + 1)) - fstar ≤ A / (1 + min (A * η / Rd ^ 2) (η' / A) * t)) ∧
      (∀ t : ℕ, 1 ≤ t → A / (1 + min (A * η / Rd ^ 2) (η' / A) * t) ≤
        max (4 * Rd ^ 2 * Lmax L * (Lmin L ^ 2 + Lf ^ 2) /
            (Lmin L ^ 2 * (1 - Real.sqrt m * γ) ^ 2))
          (2 * A ^ 2 / (Lmin L * r ^ 2)) * m ^ 2 / t)) := by sorry

end TSDRiem
