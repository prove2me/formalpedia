-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_gadForwardDiagonalOptimizer
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.gadForwardDiagonalOptimizer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:51:51.082368+00:00
-- url     : https://prove2.me/theorems/5fda5c7b-82fb-44e1-b8fa-3400e5417512
-- title:
--   Global diagonal forward optimizer for GAD
-- statement:
--   For every physical thermal GAD channel with survival $\eta\in[0,1]$ and excited environment population $\alpha\in[0,1]$, there exists $p\in[0,1]$ such that
--
--   $$I(D_{\eta,\alpha},\rho)\le I(D_{\eta,\alpha},\operatorname{diag}(1-p,p))\qquad\text{for every density input }\rho.$$
--
--   This is the source's global input-optimality claim; the chosen diagonal input may be pure. It does not assert that dephasing improves forward information at every fixed population.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 7, appendix opening p.4 and numerical discussion p.7

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4,7: global diagonal forward optimizer for GAD, as claimed by the
source. The p.7 support is a numerical survey, not an analytic certificate;
fixed-population optimality is deliberately not asserted in this node. -/
theorem gadForwardDiagonalOptimizer (eta alpha : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1) :
    ∃ p ∈ Set.Icc (0 : ℝ) 1,
      ∀ rho : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix rho →
        forwardInfo (gadDilation eta alpha) rho ≤
          forwardInfo (gadDilation eta alpha) (diagonalInput p) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
