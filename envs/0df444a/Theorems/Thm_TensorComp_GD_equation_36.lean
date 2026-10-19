-- Prove2me | Theorems.Thm_TensorComp_GD_equation_36
-- name    : TensorComp.GD.equation_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:25.589968+00:00
-- url     : https://prove2.me/theorems/bd30132e-f21a-4edc-9280-d9a05a2f0d7e
-- title:
--   (36), p. 17 — gradient identity for the sampled symmetric cubic loss
-- statement:
--   Let $U^\star,U,V\in\mathbb R^{d\times r}$, let $p>0$, and let $\Omega$ and the observed tensor $T$ be formed by symmetrizing arbitrary sampling and noise values on sorted triples. For the cubic sampled loss $f$, the directional derivative at $U$ in direction $V$ is
--   $$Df(U)[V]=\sum_{i=1}^d\sum_{s=1}^r\left[\frac1p P_\Omega(T(U)-T)\times_1^{\mathrm{seq}}U\times_2^{\mathrm{seq}}U\right]_{is}V_{is}.$$
--   This identifies the matrix used by Algorithm 1 as the Frobenius gradient of the loss.
--
--   **Formalization Note.** Symmetry is built into the sorted-triple construction. Without symmetric sampling and noise, the identity can fail.
-- source:
--   Cai, Li, Poor, Chen, Nonconvex Low-Rank Tensor Completion from Noisy Data, arXiv:1911.04436v2, p. 17, equation (36)

import Mathlib
import Definitions.Def_TensorComp_GD_Model

namespace TensorComp.GD

/-- Cai–Li–Poor–Chen, arXiv:1911.04436v2, equation (36), p. 17.
The sorted-coordinate sampling model makes the mask and observation symmetric. -/
theorem equation_36 {d r : ℕ} (Ustar U V : Factor d r)
    (p : ℝ) (hp : 0 < p)
    (χ : SortedIdx d → Bool) (E : SortedIdx d → ℝ) :
    let Ω := omegaOf χ
    let T := obs Ustar χ E
    fderiv ℝ (fun W : Factor d r => loss p Ω T W) U V =
      ∑ i : Fin d, ∑ s : Fin r,
        (1 / p * seqProd (projOmega Ω (cpTensor U - T)) U U i s) * V i s := by sorry

end TensorComp.GD
