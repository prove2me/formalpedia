-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P04_sonicHorizon
-- name    : QAlgorithms.Papers.Independent.Next46.P04.sonicHorizon
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:37:24.572749+00:00
-- url     : https://prove2.me/theorems/53b23223-02bb-4fe6-9a90-fb11c2c3e217
-- title:
--   Sonic horizon and the two flow regions
-- statement:
--   Work in the reduced, dispersionless conformal acoustic model with instantaneous quench and no backscattering. Let $V<0$, $a=|V|$, $c_{\rm in}>a$, $\kappa,n,\ell_\perp,m,\hbar,k_B>0$, and $n_1=n\ell_\perp^2$. The constant flow is $V$ and
--   $$c(x)=a\left(1+\frac23\tanh z(x)\right),\qquad z(x)=\frac{3\kappa x}{2a}.$$
--   The assertions are exact within this reduced model; they give no microscopic approximation error. No physical value of the discontinuous quench at $t=0$ is assigned.
--
--   Before the quench, the flow is subsonic because $c_{\rm in}>a$. After the quench,
--   $$c(0)=a,\qquad x>0\Longrightarrow c(x)>a,\qquad x<0\Longrightarrow 0<c(x)<a,\qquad c'(0)=\kappa.$$
--   These identities identify the sonic horizon and its surface-gravity normalization; they make no separate assertion about particle creation.
-- source:
--   Ramp-up of Hawking radiation in Bose-Einstein condensate analogue black holes, arXiv:2005.04443v3, PDF p. 2, Following (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P04

namespace QAlgorithms.Papers.Independent.Next46.P04

noncomputable section

open Filter

/-- PDF p. 2, paragraph following (4): horizon and sub/supersonic regions,
including the normalization of surface gravity. No quench-time speed is defined. -/
theorem sonicHorizon (p : AcousticModel) :
    a p < p.cin ∧ soundSpeed p 0 = a p ∧
    (∀ x : ℝ, 0 < x → a p < soundSpeed p x) ∧
    (∀ x : ℝ, x < 0 → 0 < soundSpeed p x ∧ soundSpeed p x < a p) ∧
    HasDerivAt (soundSpeed p) p.kappa 0 := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P04
