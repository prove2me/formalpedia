-- Prove2me | Theorems.Thm_PureDPQR_lemma_14
-- name    : PureDPQR.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:59:38.79645+00:00
-- url     : https://prove2.me/theorems/39dc87f5-f910-430d-89b5-951807a5c4b3
-- title:
--   Lemma 14, p.16 — sparse Laplace input smoothing: $Q_{v'}(F)\le e^{L\|v'-v\|_1}Q_v(F)$, $Q_v\ge(1-\pi)^dp_v$, $\|Q_v-p_v\|_{\mathrm{TV}}\le d\pi$
-- statement:
--   **Lemma 14** (Sparse Smoothing of an Iterative Procedure). Let $Y$ be a finite set and $(p_v)_{v\in\mathbb R^d}$ a family of laws on $Y$ such that $v\mapsto p_v(y)$ is strictly positive and twice continuously differentiable for every $y$. Let $\pi\in(0,1)$, $0<r\le\kappa$, and suppose
--
--   $$\partial^2_{v_j}\log p_v(y)\ge-r^2\quad\text{for all }v\in\mathbb R^d,\ j\in[d],\ y\in Y. \tag{4.4}$$
--
--   Let $Q_v(y)=\mathbb E_Z[p_{v+Z}(y)]$ with $Z_j$ i.i.d. $(1-\pi)\delta_0+\pi\mathrm{Lap}(\kappa)$, and set $L:=\kappa+r\sqrt{2\log(4/\pi)}$. Then:
--
--   1. (log-Lipschitz bound) for all $v,v'\in\mathbb R^d$ and every event $F\subseteq Y$, $\;Q_{v'}(F)\le e^{L\|v'-v\|_1}Q_v(F)$;
--   2. (pointwise domination) for every $y$, $\;Q_v(y)\ge(1-\pi)^dp_v(y)$;
--   3. (total variation proximity) $\;\|Q_v-p_v\|_{\mathrm{TV}}\le d\pi$.
--
--   The lemma turns a uniform lower bound on log-curvature into a pure-privacy bound whose constant does not depend on the number of rounds; it is the central analytic ingredient of the paper.
--
--   **Formalization Note** $Y$ plays the role of the transcript space $Y^T$. Events are finite sets of outcomes, $Q_v(F)=\sum_{y\in F}Q_v(y)$. $\partial^2_{v_j}$ is the second derivative of the coordinate slice. $\kappa>0$ (Procedure 3) follows from $0<r\le\kappa$.
--
--   Differences from the source:
--   - generalization: the transcript law (4.1) of a T-round procedure, strictly positive and C² in v (§4 standing assumption, p.15) → any family p : ℝ^d → Y → ℝ of positive laws on a finite type Y, C² in v; reason: the proof uses only positivity, C² and Σ_y p_v(y) = 1; every transcript law of Procedure 2 on a finite Y^T is such a family
--   - reading: the transcript space Y^T → a finite type (Fintype Y); reason: the proof calls it "the finite transcript space Y^T" (p.17) and uses Lemma 12, which is for finite laws
--   - encoding: events F ⊆ Y^T, ∂²_{v_j}, ‖·‖_TV → F : Finset Y with Q_v(F) = Σ_{y∈F} Q_v(y); the second derivative of the coordinate slice; tvDist; reason: every subset of a finite type is a Finset; same quantities
--   - encoding: Lap(κ) of rate κ → PrivLearn.Generic.laplace κ⁻¹ (scale parameter); reason: the published Laplace law is parametrized by its scale; same law
--   - encoding: 1-based coordinates [d] → Fin d; reason: Lean convention
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Lemma 14, p.16 (PDF p.17); §4 standing assumption, p.15; Procedure 3, p.16

import Mathlib
import Definitions.Def_PureDPQR_smoothed
import Definitions.Def_PureDPQR_tvDist

namespace PureDPQR

/-- **Lemma 14** (Sparse Smoothing of an Iterative Procedure), p.16 (PDF p.17).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"Suppose the original transcript law p_v(y) satisfies, for some 0 < r ≤ κ,
∂²_{v_j} log p_v(y) ≥ −r² for all v ∈ R^d, j ∈ [d], y ∈ Y^T. (4.4) Set L := κ + r √(2 log(4/π)).
(4.5) Then, distribution Q_v satisfies the following properties: (i) Pure privacy / Log-Lipschitz
bound: For all v, v′ ∈ R^d and every event F ⊆ Y^T, Q_{v′}(F) ≤ e^{L‖v′−v‖₁} Q_v(F). (4.6)
(ii) Pointwise domination: For every y ∈ Y^T, Q_v(y) ≥ (1 − π)^d p_v(y). (4.7) (iii) Total
variation proximity: The total variation distance satisfies ‖Q_v − p_v‖_TV ≤ dπ. (4.8)"

Standing assumptions of §4 (p.15): "for every fixed transcript y, we assume that v ↦ p_v(y) is
strictly positive and twice continuously differentiable on R^d"; Procedure 3 (p.16): "public
π ∈ (0, 1) and κ > 0".

**Formalization Note.**
* The finite transcript space `Y^T` is an arbitrary finite type `Y`, and the transcript law is any
  family `p : ℝ^d → Y → ℝ` of laws on `Y` (positive, summing to `1`) that is `C²` in `v`; the
  product form (4.1) of an iterative procedure is not required (a generalization: every transcript
  law of Procedure 2 on a finite `Y^T` is such a family).
* `π` is written `pert`. `Q_v(y)` is `smoothed p pert κ v y = E_Z[p_{v+Z}(y)]` (4.3);
  `Q_v(F) = ∑_{y ∈ F} Q_v(y)` for every subset `F` (a `Finset` of the finite type);
  `‖v′ − v‖₁ = ∑_j |v′_j − v_j|`; `‖Q_v − p_v‖_TV` is `tvDist` (p.14).
* `∂²_{v_j}` is the second derivative of the slice `x ↦ log p(update v j x)(y)` at `x = v_j`.
* `κ > 0` of Procedure 3 follows from `0 < r ≤ κ` and is not repeated. -/
theorem lemma_14 {d : ℕ} {Y : Type*} [Fintype Y] (p : (Fin d → ℝ) → Y → ℝ)
    (hpos : ∀ v y, 0 < p v y) (hsum : ∀ v, ∑ y, p v y = 1)
    (hC2 : ∀ y, ContDiff ℝ 2 (fun v => p v y))
    (pert κ r : ℝ) (hpert : 0 < pert) (hpert1 : pert < 1) (hr : 0 < r) (hrκ : r ≤ κ)
    (hcurv : ∀ (v : Fin d → ℝ) (j : Fin d) (y : Y),
      -(r ^ 2) ≤ deriv^[2] (fun x => Real.log (p (Function.update v j x) y)) (v j)) :
    let L : ℝ := κ + r * Real.sqrt (2 * Real.log (4 / pert))
    (∀ (v v' : Fin d → ℝ) (F : Finset Y),
        ∑ y ∈ F, smoothed p pert κ v' y ≤
          Real.exp (L * ∑ j, |v' j - v j|) * ∑ y ∈ F, smoothed p pert κ v y) ∧
      (∀ (v : Fin d → ℝ) (y : Y), (1 - pert) ^ d * p v y ≤ smoothed p pert κ v y) ∧
      (∀ v : Fin d → ℝ, tvDist (smoothed p pert κ v) (p v) ≤ (d : ℝ) * pert) := by sorry

end PureDPQR
