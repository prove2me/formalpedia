-- Prove2me | Theorems.Thm_ProjFPOracle_lemma_4
-- name    : ProjFPOracle.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:13.497457+00:00
-- url     : https://prove2.me/theorems/ce03b87d-7499-40b9-84d6-1f044d403fec
-- title:
--   Lemma 4, p.28 — $|||(I-L_{\mathbb S,\mathbb S})^{-1}L_{\mathbb S,\perp}|||^2\le\lambda_{\max}((I-M)^{-1}(|||L|||^2I-MM^\top)(I-M)^{-\top})$
-- statement:
--   Let $\mathbb X$ be a real Hilbert space, $\mathbb S$ a subspace with orthonormal basis $\varphi_1,\dots,\varphi_d$ ($d\ge1$), $L$ a bounded operator on $\mathbb X$ with $I-L$ boundedly invertible, and $M=\Phi_dL\Phi_d^*$ with $\kappa(M)<1$. Then
--   $$
--   |||(I-L_{\mathbb S,\mathbb S})^{-1}L_{\mathbb S,\perp}|||_{\mathbb X}^2\le\lambda_{\max}\Big((I_d-M)^{-1}\big(|||L|||_{\mathbb X}^2I_d-MM^\top\big)(I_d-M)^{-\top}\Big),
--   $$
--   where $|||L|||_{\mathbb X}$ is the operator norm of $L$ on $\mathbb X$ (not of $M$).
--
--   Combined with Lemma 3 it gives the approximation-error bound (45a) with the factor $\alpha(M,|||L|||_{\mathbb X})$, which depends on $L$ only through $M$ and its norm.
--
--   Differences from the source:
--   - reading: Lemma/Theorem statement without the standing assumptions of §2.1 and §5.1 → hypotheses IsUnit (1 − L) and κ(M) < 1; reason: p.7 "We assume that the operator I − L has a bounded inverse"; p.28 "our assumption that κ(M) < 1"; the statements need both
--   - generalization: a separable Hilbert space 𝕏 with an orthogonal basis {φ_j}_{j≥1} of 𝕏 such that 𝕊 = span{φ_1, …, φ_d} → any complete real inner product space 𝕏 (not necessarily separable) and an orthonormal basis φ_1, …, φ_d of 𝕊 only; reason: the statements involve only φ_1, …, φ_d; every paper instance is an instance of the Lean statement
--   - encoding: d unrestricted → 1 ≤ d; reason: λ_max and κ(M) are undefined for a 0 × 0 matrix (and η = 1/(c₀σ_L√(dn)) at d = 0); a nondegeneracy condition
--   - encoding: (I − L_{𝕊,𝕊})⁻¹ → Ring.inverse (1 − L_{𝕊,𝕊}) in the ring of bounded operators; reason: I − L_{𝕊,𝕊} is invertible under κ(M) < 1 (p.28), so Ring.inverse is its inverse; no instance changes
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, Lemma 4, p.28

import Mathlib
import Definitions.Def_LowRankMEG_lam
import Definitions.Def_ProjFPOracle_projMat
import Definitions.Def_ProjFPOracle_kappa
import Definitions.Def_ProjFPOracle_LSperp

namespace ProjFPOracle

/-- **Lemma 4** (Mou, Pananjady & Wainwright, *Optimal Oracle Inequalities for Projected
Fixed-Point Equations*, arXiv:2012.05299v1, Lemma 4, p.28): "Under the set-up above, we have
`|||(I − L_{𝕊,𝕊})⁻¹ L_{𝕊,⊥}|||²_𝕏 ≤ λ_max((I_d − M)⁻¹(|||L|||²_𝕏 I_d − M Mᵀ)(I_d − M)⁻ᵀ)`."

The set-up (§2.1, p.7; §5.1.1, pp.27–28): `𝕏` a real Hilbert space, `𝕊` with orthonormal basis
`φ_1, …, φ_d` (`1 ≤ d`), `I − L` boundedly invertible, `M = Φ_d L Φ_d^*` with `κ(M) < 1`.

**Formalization Note** `(I − L_{𝕊,𝕊})⁻¹` is `Ring.inverse (1 - LSS φ L)`, the true inverse under
`κ(M) < 1` (p.28). `λ_max` is the published `LowRankMEG.lam · 1` (largest eigenvalue of the
symmetric matrix shown); `(I_d − M)⁻¹` is Mathlib's matrix inverse, the true inverse under
`κ(M) < 1`. `|||L|||_𝕏 = ‖L‖` is the operator norm of `L` on `𝕏`, not of `M`. -/
theorem lemma_4 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {S : Submodule ℝ X} {d : ℕ} (φ : OrthonormalBasis (Fin d) ℝ S) (L : X →L[ℝ] X)
    (hd : 1 ≤ d) (hL : IsUnit (1 - L)) (hκ : kappa (projMat L φ) < 1) :
    ‖Ring.inverse (1 - LSS φ L) * LSperp φ L‖ ^ 2 ≤
      LowRankMEG.lam ((1 - projMat L φ)⁻¹ *
        (‖L‖ ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) - projMat L φ * (projMat L φ).transpose) *
        ((1 - projMat L φ)⁻¹).transpose) 1 := by sorry

end ProjFPOracle
