-- Prove2me | Theorems.Thm_TSDRiem_lemma_4_1
-- name    : TSDRiem.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:30:19.704605+00:00
-- url     : https://prove2.me/theorems/0820a5ed-0ad9-4a16-988f-b11aeb1c3d30
-- title:
--   Lemma 4.1 — deterministic sufficient decrease template, (9) and (11)
-- statement:
--   **Lemma 4.1 (Deterministic Sufficient Decrease Template).** Consider a run of Algorithm 1 for which Assumption 4.1 holds with constants $L_1,\dots,L_m$, and suppose the stepsizes are $\eta_{t,k}=1/L_k$ for all $t\ge1$, $k\in[m]$. Then for every $t\ge1$:
--
--   1. the decrease over one outer iteration satisfies
--   $$
--   f(y^{t,0})-f(y^{t,m})\ge\sum_{k\in[m]}\frac1{2L_k}\big\|P^{y^{t,k-1}}_k\nabla f(y^{t,k-1})\big\|^2_{y^{t,k-1}} ;\tag{9}
--   $$
--   2. if $C\ge0$ is such that for every $k\in[m]$
--   $$
--   \big\|P_{t,k}\nabla f(y^{t,0})-P_{t,k}\Gamma^{y^{t,0}}_{y^{t,k-1}}\nabla f(y^{t,k-1})\big\|^2_{y^{t,0}}\le C\sum_{j\in[k]}\big\|P^{y^{t,j-1}}_j\nabla f(y^{t,j-1})\big\|^2_{y^{t,j-1}} ,\tag{10}
--   $$
--   then
--   $$
--   f(y^{t,0})-f(y^{t,m})\ge\frac1{4L_{\max}(1+Cm)}\,\|\nabla f(y^{t,0})\|^2_{y^{t,0},\mathcal P} .\tag{11}
--   $$
--
--   Here $P_{t,k}=\Gamma^{y^{t,0}}_{y^{t,k-1}}P^{y^{t,k-1}}_k\Gamma^{y^{t,k-1}}_{y^{t,0}}$ and $\|\cdot\|_{y^{t,0},\mathcal P}$ is the seminorm built from the $P_{t,k}$.
--
--   The lemma converts block smoothness into a decrease bound measured in the seminorm $\|\cdot\|_{y^{t,0},\mathcal P}$. Condition (10) controls how much the gradient changes along the inner loop, and Lemma 4.3 verifies it.
--
--   **Formalization Note** The setting is the abstract Riemannian setting, and the run is any run of Algorithm 1 along which the hypotheses hold. Lean's `k : Fin m` is the paper's step $k+1$, so `Finset.Iic k` is $[k]$.
--
--   Differences from the source:
--   - generalization: a connected, geodesically complete Riemannian manifold with its Riemannian distance, exponential map, parallel transport and Riemannian gradient → an abstract metric space with finite-dimensional inner-product fibres, an exp map and isometric transports satisfying (A1) and (A2), and any function f with any gradient field; reason: Mathlib has no exponential map or parallel transport, and the paper's objects satisfy (A1), (A2) and isometry by the §2 facts (p.4)
--   - generalization: Assumption 4.1 for the iterates of Algorithm 1 under a selection rule P → Assumption 4.1 along one given run whose subspaces are data; reason: every run of every rule satisfying the assumption is such a run
--   - generalization: transport Γ^{y^{t,0}}_{y^{t,k−1}} along an unspecified geodesic → transport along the geodesic fixed by an arbitrary connecting vector w_{t,k} with Exp(w_{t,k}) = y^{t,0}; reason: the statement holds for every choice, so it covers whichever geodesic the paper intends
--   - generalization: "there exists some C > 0" such that (10) holds → any C ≥ 0, with (10) assumed only at the iteration t considered; reason: the proof never uses C > 0 or (10) at other iterations, and Lemma 4.4 applies the lemma with C = L_f²(m−1)/L_min², which is 0 at m = 1
--   - reading: L_max undefined in the paper → L_max = max_k L_k; reason: the proof bounds 1/(2L_k) ≥ 1/(2L_max)
--   - encoding: inner index k ∈ [m] = {1,…,m} → k : Fin m = {0,…,m−1} with y^{t,k−1} = y t k.castSucc; reason: index shift only
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Lemma 4.1, eqs. (9)–(11), p.10

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting
import Definitions.Def_TSDRiem_TSDRun
import Definitions.Def_TSDRiem_TSDRun_transportBack
import Definitions.Def_TSDRiem_TSDRun_Ptk
import Definitions.Def_TSDRiem_TSDRun_seminormP
import Definitions.Def_TSDRiem_TSDRun_BlockSmooth
import Definitions.Def_TSDRiem_Lmax

namespace TSDRiem

/-- **Lemma 4.1 (Deterministic Sufficient Decrease Template).** Suppose Assumption 4.1 holds and
the stepsizes are `η_{t,k} := 1/L_k`. Then for every `t ≥ 1`
(9) `f(y^{t,0}) − f(y^{t,m}) ≥ Σ_{k∈[m]} (1/(2L_k)) ‖P^{y^{t,k−1}}_k ∇f(y^{t,k−1})‖²`,
and if, for some `C` and every `k ∈ [m]`, (10)
`‖P_k∇f(y^{t,0}) − P_kΓ^{y^{t,0}}_{y^{t,k−1}}∇f(y^{t,k−1})‖² ≤ C Σ_{j∈[k]} ‖P^{y^{t,j−1}}_j ∇f(y^{t,j−1})‖²`,
then (11) `f(y^{t,0}) − f(y^{t,m}) ≥ (1/(4L_max(1 + Cm))) ‖∇f(y^{t,0})‖²_{y^{t,0},P}`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Lemma 4.1,
eqs. (9)–(11), p.10.

Formalization Note: the setting is the abstract `RiemSetting` (see there); the run is any run of
Algorithm 1 and Assumption 4.1 is imposed along it. Lean's `k : Fin m` is the paper's `k + 1`:
`R.y t k.castSucc = y^{t,k}`, `(R.sub t k).starProjection = P^{y^{t,k}}_{k+1}`, `Finset.Iic k` is
`[k+1]`, and `R.Ptk t k`, `R.transportBack t k` are `P_{t,k+1}`, `Γ^{y^{t,0}}_{y^{t,k}}`.
`y^{t,m}` is `R.y t (Fin.last m)`. The paper asks `C > 0`; `C ≥ 0` is allowed here
(generalization: Lemma 4.4 uses `C = L_f²(m−1)/L²_min`, which is `0` at `m = 1`). -/
theorem lemma_4_1 {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    [∀ x, FiniteDimensional ℝ (T x)] (S : RiemSetting M T) (f : M → ℝ)
    (grad : (x : M) → T x) {m : ℕ} (R : TSDRun S grad m) (L : Fin m → ℝ)
    (h41 : R.BlockSmooth f L) (hstep : ∀ t, 1 ≤ t → ∀ k, R.η t k = 1 / L k)
    (t : ℕ) (ht : 1 ≤ t) :
    (∑ k : Fin m, 1 / (2 * L k) * ‖(R.sub t k).starProjection (grad (R.y t k.castSucc))‖ ^ 2 ≤
        f (R.y t 0) - f (R.y t (Fin.last m))) ∧
      ∀ C : ℝ, 0 ≤ C →
        (∀ k : Fin m,
          ‖R.Ptk t k (grad (R.y t 0)) - R.Ptk t k (R.transportBack t k (grad (R.y t k.castSucc)))‖ ^ 2 ≤
            C * ∑ j ∈ Finset.Iic k, ‖(R.sub t j).starProjection (grad (R.y t j.castSucc))‖ ^ 2) →
        1 / (4 * Lmax L * (1 + C * m)) * R.seminormP t (grad (R.y t 0)) ^ 2 ≤
          f (R.y t 0) - f (R.y t (Fin.last m)) := by sorry

end TSDRiem
