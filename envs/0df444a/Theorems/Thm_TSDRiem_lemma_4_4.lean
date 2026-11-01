-- Prove2me | Theorems.Thm_TSDRiem_lemma_4_4
-- name    : TSDRiem.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:30:25.510593+00:00
-- url     : https://prove2.me/theorems/3ac8e175-f87f-4579-9fff-7c1bf0b1fccd
-- title:
--   Lemma 4.4 — two-case sufficient decrease (13)/(14) (corrected: $\sqrt m\,\gamma\le1$ in part 1)
-- statement:
--   **Lemma 4.4 (corrected in part 1).** Let $\nabla f$ be $L_f$-smooth, and consider a run of Algorithm 1 along which Assumption 4.1 holds with constants $L_1,\dots,L_m$, the stepsizes are $\eta_{t,k}=1/L_k$, and the selection is $(\gamma,r)$-gap ensuring (Assumption 4.2). Let
--
--   $$
--   \eta:=\frac{L_{\min}^2(1-\sqrt m\,\gamma)^2}{4L_{\max}\big(L_{\min}^2+L_f^2(m-1)m\big)},\qquad \eta':=\frac{L_{\min}r^2}{2m}.
--   $$
--
--   Then for every iteration $t\ge1$:
--
--   1. if $\sqrt m\,\gamma\le1$ and $\sum_{k\in[m]}d(y^{t,k-1},y^{t,k})\le r$, then $f(y^{t,0})-f(y^{t,m})\ge\eta\,\|\nabla f(y^{t,0})\|^2_{y^{t,0}}$; (13)
--   2. if $\sum_{k\in[m]}d(y^{t,k-1},y^{t,k})>r$, then $f(y^{t,0})-f(y^{t,m})\ge\eta'$. (14)
--
--   Every outer iteration therefore makes progress: either proportional to the squared gradient norm at its starting point, when the inner loop stays short, or a fixed amount $\eta'$, when it travels farther than $r$. This dichotomy is what replaces the Euclidean sufficient decrease inequality in the proof of Theorem 4.5.
--
--   **Formalization Note** Lean's `k : Fin m` is the paper's step $k+1$, so `dist (y t k.castSucc) (y t k.succ)` is $d(y^{t,k},y^{t,k+1})$.
--
--   Differences from the source:
--   - correction: part 1 for arbitrary γ ∈ (0, 1] → part 1 under the additional hypothesis √m·γ ≤ 1, part 2 as printed; reason: the printed part 1 is false. Counterexample: ℝ² with Exp_x(v) = x + v, f = ½‖x‖², m = 2, L_k = 1, stepsizes 1, γ = 1, any r > 0, both selected lines orthogonal to y^{t,0} = (1, 0); every step is zero, Assumptions 4.1 and 4.2 hold (P′ = Π_{e₁}, Π_{e₂}), Σ_k d = 0 ≤ r, but f(y^{t,0}) − f(y^{t,m}) = 0 < η = (√2 − 1)²/12
--   - generalization: a connected, geodesically complete Riemannian manifold with its Riemannian distance, exponential map, parallel transport and Riemannian gradient → an abstract metric space with finite-dimensional inner-product fibres, an exp map and isometric transports satisfying (A1) and (A2), and any function f with any gradient field; reason: Mathlib has no exponential map or parallel transport, and the paper's objects satisfy (A1), (A2) and isometry by the §2 facts (p.4)
--   - generalization: Assumptions 4.1 and 4.2 for the iterates of Algorithm 1 under a selection rule P → both assumptions along one given run whose subspaces are data; reason: every run of every rule satisfying them is such a run
--   - generalization: transport Γ^{y^{t,0}}_{y^{t,k−1}} along an unspecified geodesic → transport along the geodesic fixed by an arbitrary connecting vector w_{t,k}; reason: the statement holds for every choice
--   - reading: L_f-smoothness not printed in the lemma → f L_f-smooth in the sense of (2); reason: §4.1 assumes L_f-smoothness throughout (p.9, there "in the sense of (4)", the consequence of (2)), L_f enters η, and the proof uses Lemma 4.3, which needs (2)
--   - reading: stepsize not printed in the lemma → η_{t,k} = 1/L_k; reason: the proof uses (9) and (11) of Lemma 4.1, which assume it
--   - reading: L_max, L_min undefined in the paper → max_k L_k and min_k L_k; reason: the values the proofs of Lemmas 4.1 and 4.3 use
--   - encoding: inner index k ∈ [m] = {1,…,m} → k : Fin m = {0,…,m−1}; reason: index shift only
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Lemma 4.4, eqs. (13)–(14), p.13

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting
import Definitions.Def_TSDRiem_RiemSetting_IsLSmooth
import Definitions.Def_TSDRiem_TSDRun
import Definitions.Def_TSDRiem_TSDRun_BlockSmooth
import Definitions.Def_TSDRiem_TSDRun_GapEnsuring
import Definitions.Def_TSDRiem_eta
import Definitions.Def_TSDRiem_etaPrime

namespace TSDRiem

/-- **Lemma 4.4 (corrected: `√m γ ≤ 1` in part 1).** Suppose `f` is `L_f`-smooth, Assumption 4.1 holds
(stepsizes `1/L_k`) and the rule is `(γ, r)`-gap ensuring (Assumption 4.2). Let
`η := L²_min(1 − √m γ)² / (4L_max(L²_min + L²_f(m − 1)m))` and `η′ := L_min r²/(2m)`. Then for any
iteration `t ≥ 1`:
1. if `√m γ ≤ 1` and `Σ_{k∈[m]} d(y^{t,k−1}, y^{t,k}) ≤ r`, then (13)
   `f(y^{t,0}) − f(y^{t,m}) ≥ η‖∇f(y^{t,0})‖²`;
2. if `Σ_{k∈[m]} d(y^{t,k−1}, y^{t,k}) > r`, then (14) `f(y^{t,0}) − f(y^{t,m}) ≥ η′`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Lemma 4.4,
eqs. (13)–(14), p.13.

Formalization Note (correction): `√m γ ≤ 1` is added to part 1 only (part 2 holds as printed).
Without it part 1 is false: in ℝ² with
`f = ½‖x‖²`, `m = 2`, `L_k = 1`, `γ = 1`, both selected lines orthogonal to `y^{t,0} = (1, 0)`,
every step is zero, Assumption 4.2 holds, and `f(y^{t,0}) − f(y^{t,m}) = 0 < η`.
Readings: `L_f`-smoothness (2) is the standing assumption of §4.1 (p.9) and enters `η`; the
stepsize `1/L_k` is the one of Lemma 4.1, whose (9) and (11) the proof uses. Lean's `k : Fin m`
is the paper's `k + 1`, so `dist (R.y t k.castSucc) (R.y t k.succ)` is `d(y^{t,k}, y^{t,k+1})`. -/
theorem lemma_4_4 {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    [∀ x, FiniteDimensional ℝ (T x)] (S : RiemSetting M T) (f : M → ℝ)
    (grad : (x : M) → T x) (Lf : ℝ) (hsmooth : S.IsLSmooth grad Lf) {m : ℕ}
    (R : TSDRun S grad m) (L : Fin m → ℝ) (h41 : R.BlockSmooth f L)
    (hstep : ∀ t, 1 ≤ t → ∀ k, R.η t k = 1 / L k) (γ r : ℝ) (h42 : R.GapEnsuring γ r)
    (t : ℕ) (ht : 1 ≤ t) :
    (Real.sqrt m * γ ≤ 1 → ∑ k : Fin m, dist (R.y t k.castSucc) (R.y t k.succ) ≤ r →
        eta m L Lf γ * ‖grad (R.y t 0)‖ ^ 2 ≤ f (R.y t 0) - f (R.y t (Fin.last m))) ∧
      (r < ∑ k : Fin m, dist (R.y t k.castSucc) (R.y t k.succ) →
        etaPrime m L r ≤ f (R.y t 0) - f (R.y t (Fin.last m))) := by sorry

end TSDRiem
