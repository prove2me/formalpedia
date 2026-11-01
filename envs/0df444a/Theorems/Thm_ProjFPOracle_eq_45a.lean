-- Prove2me | Theorems.Thm_ProjFPOracle_eq_45a
-- name    : ProjFPOracle.eq_45a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:08.551712+00:00
-- url     : https://prove2.me/theorems/9dc8d199-8dd1-45a4-9ced-355a46e3171d
-- title:
--   Eq. (45a), p.27 — approximation error $\|\bar v-v^*\|^2\le\alpha(M,|||L|||_{\mathbb X})\inf_{v\in\mathbb S}\|v-v^*\|^2$
-- statement:
--   Let $\mathbb X$ be a real Hilbert space, $\mathbb S$ a subspace with orthonormal basis $\varphi_1,\dots,\varphi_d$ ($d\ge1$), $L$ a bounded operator with $I-L$ boundedly invertible, $b\in\mathbb X$ and $v^*=Lv^*+b$, and $M=\Phi_dL\Phi_d^*$ with $\kappa(M)<1$. Then the projected fixed point $\bar v$ satisfies
--   $$
--   \|\bar v-v^*\|^2\le\alpha\big(M,|||L|||_{\mathbb X}\big)\inf_{v\in\mathbb S}\|v-v^*\|^2,
--   $$
--   where $\alpha(M,s)=1+\lambda_{\max}\big((I-M)^{-1}(s^2I_d-MM^\top)(I-M)^{-\top}\big)$.
--
--   This is the deterministic half of Theorem 1: the oracle term $\alpha(M,|||L|||_{\mathbb X})\inf_{v\in\mathbb S}\|v-v^*\|^2$ bounds the price of solving the projected instead of the original equation.
--
--   Differences from the source:
--   - reading: Lemma/Theorem statement without the standing assumptions of §2.1 and §5.1 → hypotheses IsUnit (1 − L) and κ(M) < 1; reason: p.7 "We assume that the operator I − L has a bounded inverse"; p.28 "our assumption that κ(M) < 1"; the statements need both
--   - generalization: "under the conditions of the theorem" (Theorem 1: observations, Assumption 1(W), sample size) → only the deterministic standing assumptions (𝕏, 𝕊, L, b, v*, κ(M) < 1); reason: (45a) involves no observation; the conditions of the theorem include these
--   - generalization: a separable Hilbert space 𝕏 with an orthogonal basis {φ_j}_{j≥1} of 𝕏 such that 𝕊 = span{φ_1, …, φ_d} → any complete real inner product space 𝕏 (not necessarily separable) and an orthonormal basis φ_1, …, φ_d of 𝕊 only; reason: the statements involve only φ_1, …, φ_d; every paper instance is an instance of the Lean statement
--   - encoding: d unrestricted → 1 ≤ d; reason: λ_max and κ(M) are undefined for a 0 × 0 matrix (and η = 1/(c₀σ_L√(dn)) at d = 0); a nondegeneracy condition
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, Eq. (45a), p.27

import Mathlib
import Definitions.Def_ProjFPOracle_projMat
import Definitions.Def_ProjFPOracle_kappa
import Definitions.Def_ProjFPOracle_alphaFactor
import Definitions.Def_ProjFPOracle_vbar

namespace ProjFPOracle

/-- **The approximation-error bound, Eq. (45a)** (Mou, Pananjady & Wainwright, *Optimal Oracle
Inequalities for Projected Fixed-Point Equations*, arXiv:2012.05299v1, Eq. (45a), p.27): "under the
conditions of the theorem, we prove that the approximation error is upper bounded as
`‖v̄ − v^*‖² ≤ α(M, |||L|||_𝕏) inf_{v∈𝕊} ‖v − v^*‖²`."

The bound is deterministic: it involves no observation. Standing assumptions (§2.1, p.7; p.28):
`𝕏` a real Hilbert space, `𝕊` with orthonormal basis `φ_1, …, φ_d` (`1 ≤ d`), `I − L` boundedly
invertible, `v^* = L v^* + b`, and `κ(M) < 1` for `M = Φ_d L Φ_d^*`.

**Formalization Note** `α(M, s) = 1 + λ_max((I − M)⁻¹(s² I_d − M Mᵀ)(I − M)⁻ᵀ)` is `alphaFactor`,
evaluated at `s = ‖L‖`, the operator norm of `L` on `𝕏`. The infimum is over the subtype `𝕊`. -/
theorem eq_45a {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) (L : X →L[ℝ] X) (b vstar : X)
    (hd : 1 ≤ d) (hL : IsUnit (1 - L)) (hfix : vstar = L vstar + b)
    (hκ : kappa (projMat L φ) < 1) :
    ‖vbar L b φ - vstar‖ ^ 2 ≤
      alphaFactor (projMat L φ) ‖L‖ * ⨅ v : S, ‖(v : X) - vstar‖ ^ 2 := by sorry

end ProjFPOracle
