-- Prove2me | Theorems.Thm_TSDRiem_lemma_4_3
-- name    : TSDRiem.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:23.575959+00:00
-- url     : https://prove2.me/theorems/26ce8dfe-118d-4862-aa62-b3f2b01a8e18
-- title:
--   Lemma 4.3 — condition (10) holds with $C=L_f^2(m-1)/L_{\min}^2$
-- statement:
--   **Lemma 4.3.** Let $\nabla f$ be $L_f$-smooth, and consider a run of Algorithm 1 along which Assumption 4.1 holds with constants $L_1,\dots,L_m$ and the stepsizes are $\eta_{t,k}=1/L_k$. Then for every $t\ge1$ and every $k\in[m]$,
--
--   $$
--   \big\|P_{t,k}\nabla f(y^{t,0})-P_{t,k}\Gamma^{y^{t,0}}_{y^{t,k-1}}\nabla f(y^{t,k-1})\big\|^2_{y^{t,0}}\le\frac{L_f^2(m-1)}{L_{\min}^2}\sum_{j\in[k-1]}\big\|P^{y^{t,j-1}}_j\nabla f(y^{t,j-1})\big\|^2_{y^{t,j-1}} .
--   $$
--
--   The sum over $j\in[k-1]=\{1,\dots,k-1\}$ is empty for $k=1$. Since $[k-1]\subseteq[k]$, the lemma shows that condition (10) of Lemma 4.1 holds with $C=L_f^2(m-1)/L_{\min}^2$: the gradient seen at the start of the inner loop and the transported gradient at step $k$ differ by at most the progress already made.
--
--   **Formalization Note** Lean's `k : Fin m` is the paper's step $k+1$, so `Finset.Iio k` is $[k-1]$.
--
--   Differences from the source:
--   - generalization: a connected, geodesically complete Riemannian manifold with its Riemannian distance, exponential map, parallel transport and Riemannian gradient → an abstract metric space with finite-dimensional inner-product fibres, an exp map and isometric transports satisfying (A1) and (A2), and any function f with any gradient field; reason: Mathlib has no exponential map or parallel transport, and the paper's objects satisfy (A1), (A2) and isometry by the §2 facts (p.4)
--   - generalization: Assumption 4.1 for the iterates of Algorithm 1 under a selection rule P → Assumption 4.1 along one given run whose subspaces are data; reason: every run of every rule satisfying the assumption is such a run
--   - generalization: transport Γ^{y^{t,0}}_{y^{t,k−1}} along an unspecified geodesic → transport along the geodesic fixed by an arbitrary connecting vector w_{t,k}; reason: the statement holds for every choice
--   - reading: stepsize not printed in the lemma → η_{t,k} = 1/L_k; reason: the proof uses it ("we used the fact that y^j = Exp_{y^{j−1}}(−(1/L_j)P∇f(y^{j−1}))", p.13), and it is the stepsize of Lemma 4.1
--   - reading: L_min undefined in the paper → L_min = min_k L_k; reason: the proof bounds 1/L_j² ≤ 1/L_min²
--   - encoding: inner index k ∈ [m] = {1,…,m} → k : Fin m = {0,…,m−1}, [k−1] = Finset.Iio k; reason: index shift only
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Lemma 4.3, pp.12–13

import Mathlib
import Definitions.Def_TSDRiem_RiemSetting
import Definitions.Def_TSDRiem_RiemSetting_IsLSmooth
import Definitions.Def_TSDRiem_TSDRun
import Definitions.Def_TSDRiem_TSDRun_transportBack
import Definitions.Def_TSDRiem_TSDRun_Ptk
import Definitions.Def_TSDRiem_TSDRun_BlockSmooth
import Definitions.Def_TSDRiem_Lmin

namespace TSDRiem

/-- **Lemma 4.3.** Suppose `f` is `L_f`-smooth and Assumption 4.1 holds (stepsizes `1/L_k`). Then
for any `t ≥ 1` and `k ∈ [m]`, the iterates of Algorithm 1 satisfy
`‖P_{t,k}∇f(y^{t,0}) − P_{t,k}Γ^{y^{t,0}}_{y^{t,k−1}}∇f(y^{t,k−1})‖²
  ≤ (L_f²(m − 1)/L²_min) Σ_{j∈[k−1]} ‖P^{y^{t,j−1}}_{t,j}∇f(y^{t,j−1})‖²`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Lemma 4.3, p.12.

Formalization Note: Lean's `k : Fin m` is the paper's `k + 1`, so `Finset.Iio k` is the paper's
`[k−1]` (empty for the first step). The stepsize `η_{t,k} = 1/L_k` is not printed in the lemma
but its proof uses it (p.13, "we used the fact that y^j = Exp_{y^{j−1}}(−(1/L_j)P∇f)"); it is
assumed (reading). `m − 1` is real subtraction. The abstract setting and the run are as in
`RiemSetting` and `TSDRun`; the connecting vector `w t k` fixing `Γ^{y^{t,0}}_{y^{t,k−1}}` is
arbitrary. -/
theorem lemma_4_3 {M : Type*} [MetricSpace M] {T : M → Type*}
    [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    [∀ x, FiniteDimensional ℝ (T x)] (S : RiemSetting M T) (f : M → ℝ)
    (grad : (x : M) → T x) (Lf : ℝ) (hsmooth : S.IsLSmooth grad Lf) {m : ℕ}
    (R : TSDRun S grad m) (L : Fin m → ℝ) (h41 : R.BlockSmooth f L)
    (hstep : ∀ t, 1 ≤ t → ∀ k, R.η t k = 1 / L k) (t : ℕ) (ht : 1 ≤ t) (k : Fin m) :
    ‖R.Ptk t k (grad (R.y t 0)) - R.Ptk t k (R.transportBack t k (grad (R.y t k.castSucc)))‖ ^ 2 ≤
      Lf ^ 2 * ((m : ℝ) - 1) / Lmin L ^ 2 *
        ∑ j ∈ Finset.Iio k, ‖(R.sub t j).starProjection (grad (R.y t j.castSucc))‖ ^ 2 := by sorry

end TSDRiem
