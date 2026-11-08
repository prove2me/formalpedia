-- Prove2me | Theorems.Thm_PureDPQR_lemma_13
-- name    : PureDPQR.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:59:35.016011+00:00
-- url     : https://prove2.me/theorems/abf326ec-c316-4cd3-a180-f2c3a362c289
-- title:
--   Lemma 13, p.14 — $\mathrm{KL}\ge0$, $0\le H(p)\le\log m$, $\mathrm{KL}(p\|\mathrm{Unif}([m]))\le\log m$
-- statement:
--   **Lemma 13** (Relative entropy bounds). For probability vectors $p,q\in\Delta_m$ with all $q_j>0$,
--
--   $$\mathrm{KL}(p\|q)\ge0,\qquad 0\le-\sum_{j:\,p_j>0}p_j\log p_j\le\log m,\qquad \mathrm{KL}(p\|\mathrm{Unif}([m]))\le\log m .$$
--
--   These bounds control the potential in Lemma 19 and the entropy term in Lemma 18.
--
--   **Formalization Note** $\mathrm{Unif}([m])$ is the constant vector $1/m$.
--
--   Differences from the source:
--   - encoding: 1-based coordinates of Δ_m → Fin m; reason: Lean convention
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Lemma 13, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_PureDPQR_tvDist

namespace PureDPQR

/-- **Lemma 13** (Relative entropy bounds [Ver19]), p.14 (PDF p.15).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"For probability vectors p, q ∈ ∆m with q > 0, KL(p‖q) ≥ 0. In addition,
0 ≤ −∑_{j:pj>0} pj log pj ≤ log m, KL(p‖Unif([m])) ≤ log m."

**Formalization Note.** `Δ_m` is `stdSimplex ℝ (Fin m)`; `KL(p‖q) = ∑_{j : p_j > 0} p_j log(p_j/q_j)`
is `kl p q` (defined just above the lemma, p.14); `Unif([m])` is the constant vector `1/m`. -/
theorem lemma_13 {m : ℕ} (p q : Fin m → ℝ) (hp : p ∈ stdSimplex ℝ (Fin m))
    (hq : q ∈ stdSimplex ℝ (Fin m)) (hq0 : ∀ j, 0 < q j) :
    0 ≤ kl p q ∧
      0 ≤ -∑ j ∈ Finset.univ.filter (fun j => 0 < p j), p j * Real.log (p j) ∧
      -∑ j ∈ Finset.univ.filter (fun j => 0 < p j), p j * Real.log (p j) ≤ Real.log m ∧
      kl p (fun _ => 1 / (m : ℝ)) ≤ Real.log m := by sorry

end PureDPQR
