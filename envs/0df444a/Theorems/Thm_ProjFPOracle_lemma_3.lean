-- Prove2me | Theorems.Thm_ProjFPOracle_lemma_3
-- name    : ProjFPOracle.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:09.431907+00:00
-- url     : https://prove2.me/theorems/fa22b4aa-8485-4582-8193-ac49e8626c6b
-- title:
--   Lemma 3, p.28 — $\|\bar v-v^*\|^2\le(1+|||(I-L_{\mathbb S,\mathbb S})^{-1}L_{\mathbb S,\perp}|||^2)\inf_{v\in\mathbb S}\|v-v^*\|^2$
-- statement:
--   Let $\mathbb X$ be a real Hilbert space, $\mathbb S\subseteq\mathbb X$ a subspace with orthonormal basis $\varphi_1,\dots,\varphi_d$ ($d\ge1$), $L$ a bounded operator on $\mathbb X$ with $I-L$ boundedly invertible, $b\in\mathbb X$, and $v^*$ the fixed point $v^*=Lv^*+b$. Let $M=\Phi_dL\Phi_d^*$ satisfy $\kappa(M)<1$, and let $\bar v$ be the projected fixed point. With $L_{\mathbb S,\mathbb S}=\Pi_{\mathbb S}L\Pi_{\mathbb S}$ and $L_{\mathbb S,\perp}=\Pi_{\mathbb S}L\Pi_{\mathbb S^\perp}$,
--   $$
--   \|\bar v-v^*\|^2\le\Big(1+|||(I-L_{\mathbb S,\mathbb S})^{-1}L_{\mathbb S,\perp}|||_{\mathbb X}^2\Big)\inf_{v\in\mathbb S}\|v-v^*\|^2 .
--   $$
--   Here $|||\cdot|||_{\mathbb X}$ is the operator norm on $\mathbb X$.
--
--   This is the first half of the approximation-error bound (45a): it controls the gap between the projected and the true fixed point by the best approximation error from $\mathbb S$, with a factor depending on how $L$ couples $\mathbb S^\perp$ into $\mathbb S$.
--
--   Differences from the source:
--   - reading: Lemma/Theorem statement without the standing assumptions of §2.1 and §5.1 → hypotheses IsUnit (1 − L) and κ(M) < 1; reason: p.7 "We assume that the operator I − L has a bounded inverse"; p.28 "our assumption that κ(M) < 1"; the statements need both
--   - generalization: a separable Hilbert space 𝕏 with an orthogonal basis {φ_j}_{j≥1} of 𝕏 such that 𝕊 = span{φ_1, …, φ_d} → any complete real inner product space 𝕏 (not necessarily separable) and an orthonormal basis φ_1, …, φ_d of 𝕊 only; reason: the statements involve only φ_1, …, φ_d; every paper instance is an instance of the Lean statement
--   - encoding: d unrestricted → 1 ≤ d; reason: λ_max and κ(M) are undefined for a 0 × 0 matrix (and η = 1/(c₀σ_L√(dn)) at d = 0); a nondegeneracy condition
--   - encoding: (I − L_{𝕊,𝕊})⁻¹ → Ring.inverse (1 − L_{𝕊,𝕊}) in the ring of bounded operators; reason: I − L_{𝕊,𝕊} is invertible under κ(M) < 1 (p.28), so Ring.inverse is its inverse; no instance changes
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, Lemma 3, p.28, Eq. (46)

import Mathlib
import Definitions.Def_ProjFPOracle_Phi
import Definitions.Def_ProjFPOracle_projMat
import Definitions.Def_ProjFPOracle_kappa
import Definitions.Def_ProjFPOracle_vbar
import Definitions.Def_ProjFPOracle_LSperp

namespace ProjFPOracle

/-- **Lemma 3** (Mou, Pananjady & Wainwright, *Optimal Oracle Inequalities for Projected
Fixed-Point Equations*, arXiv:2012.05299v1, Lemma 3, p.28): "The error `‖v̄ − v^*‖` between the
projected fixed point `v̄` and the original fixed point `v^*` is bounded as
`‖v̄ − v^*‖² ≤ (1 + |||(I − L_{𝕊,𝕊})⁻¹ L_{𝕊,⊥}|||²_𝕏) inf_{v∈𝕊} ‖v − v^*‖²`." (46)

Standing assumptions of §2.1 (p.7) and §5.1.2 (p.28): `𝕏` is a real Hilbert space, `𝕊` has the
orthonormal basis `φ_1, …, φ_d` (`1 ≤ d`), `I − L` has a bounded inverse, `v^* = L v^* + b`, and
`κ(M) < 1` for `M = Φ_d L Φ_d^*`.

**Formalization Note** `(I − L_{𝕊,𝕊})⁻¹` is `Ring.inverse (1 - LSS φ L)` in the ring of bounded
operators; under `κ(M) < 1` the operator `I − L_{𝕊,𝕊}` is invertible on `𝕏` (it is `I − M` on `𝕊` and
the identity on `𝕊^⊥`, p.28), so this is its true inverse. `|||·|||_𝕏` is the operator norm. The
infimum is over the subtype `𝕊`, which is nonempty, of a quantity bounded below by `0`. Separability
of `𝕏` is not assumed. -/
theorem lemma_3 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) (L : X →L[ℝ] X) (b vstar : X)
    (hd : 1 ≤ d) (hL : IsUnit (1 - L)) (hfix : vstar = L vstar + b)
    (hκ : kappa (projMat L φ) < 1) :
    ‖vbar L b φ - vstar‖ ^ 2 ≤
      (1 + ‖Ring.inverse (1 - LSS φ L) * LSperp φ L‖ ^ 2) * ⨅ v : S, ‖(v : X) - vstar‖ ^ 2 := by sorry

end ProjFPOracle
