-- Prove2me | Theorems.Thm_SolomonRWRE_SlowApproach_lemma_2_6
-- name    : SolomonRWRE.SlowApproach.lemma_2_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:51.223865+00:00
-- url     : https://prove2.me/theorems/53fa1915-9e3b-405c-84a5-2dafeb2a7a92
-- title:
--   Lemma (2.6) — small-argument comparison of transforms
-- statement:
--   With $\varphi$ the transform series of (2.5), set
--   $$
--   \psi(u)=\frac{1-\gamma}{\gamma}\sum_{j=1}^{\infty}\frac{\gamma^j}{1+\nu u\theta^j},\qquad \nu=\frac{2\theta}{(\theta-1)^2}.
--   $$
--   In the one-way-mirror parameter range $\theta>1$, $0<\gamma<1$, $\gamma\theta\ge1$, as $u\downarrow0$ one has $\varphi(u)-\psi(u)=O(u)$.
--
--   This comparison permits the later limit calculation to use the simpler series.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 12, Lemma (2.6)

import Mathlib
import Definitions.Def_SolomonRWRE_SlowApproach_Transforms
open Filter
open scoped Topology

namespace SolomonRWRE.SlowApproach

/-- Solomon, Lemma (2.6), p. 12. The transform of (2.5) differs from its comparison
series by `O(u)` as `u` decreases to zero. Formalization Note: the paper's `φ` is the
annealed transform `phi`; by Lemma (2.5) it equals `phiSeries` for every `n ≥ 1`, `u ≥ 0`,
so the statement is made on `phiSeries`. -/
theorem lemma_2_6 (γ θ : ℝ) (hθ : 1 < θ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hcritical : 1 ≤ γ * θ) :
    (fun u => phiSeries γ θ u - psi γ θ u) =O[𝓝[>] (0 : ℝ)] (fun u => u) := by sorry

end SolomonRWRE.SlowApproach
