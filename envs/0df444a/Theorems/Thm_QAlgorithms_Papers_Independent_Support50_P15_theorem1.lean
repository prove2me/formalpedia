-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_theorem1
-- name    : QAlgorithms.Papers.Independent.Support50.P15.theorem1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:35:34.772729+00:00
-- url     : https://prove2.me/theorems/45ce5d42-23ee-44c8-9555-861327957cf0
-- title:
--   Tight relative entropy bound and explicit equality witnesses
-- statement:
--   Let $d\ge2$ be a finite dimension. States are positive semidefinite complex $d\times d$ matrices of trace one. Write $S$ for entropy in nats, $D$ for Umegaki relative entropy (infinite on support failure), $H$ for binary entropy and $D_2$ for binary relative entropy. Define $M(\Delta,d)$ as the minimum of $D_2(s\|r)$ over $0\le s,r\le(d-1)/d$ satisfying $H(s)-H(r)+(s-r)\log(d-1)=\Delta$. Then
--
--   $$D(\sigma\|\rho)\ge M(S(\sigma)-S(\rho),d).$$
--
--   For every $\Delta\in[-\log d,\log d]$ equality is attainable. Every scalar minimizing pair gives the explicit commuting states $\tau_d(s),\tau_d(r)$, where $\tau_d(u)=\operatorname{diag}(1-u,u/(d-1),\ldots,u/(d-1))$; these have exactly the prescribed difference and relative entropy $M(\Delta,d)$. The infinite right endpoint is included. This identifies the sharp bound for quantum states and classical laws alike.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 4, theorem1

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Theorem 1, PDF p.4; proof pp.17--20. Both directions and the computed commuting witnesses. -/
theorem theorem1 (d : ℕ) (hd : 2 ≤ d) :
    (∀ a b : EntropyState d, tightBound d (difference a.val b.val) ≤ stateRelativeNats a b) ∧
    (∀ delta ∈ Set.Icc (-Real.log d) (Real.log d),
      ∃ a b : EntropyState d, difference a.val b.val = delta ∧ stateRelativeNats a b = tightBound d delta) ∧
    (∀ delta s r : ℝ, minimizingPair d delta s r →
      ∃ ha : IsDensityMatrix (family d s), ∃ hb : IsDensityMatrix (family d r),
        family d s * family d r = family d r * family d s ∧
        difference (family d s) (family d r) = delta ∧
        stateRelativeNats ⟨family d s, ha⟩ ⟨family d r, hb⟩ = tightBound d delta) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
