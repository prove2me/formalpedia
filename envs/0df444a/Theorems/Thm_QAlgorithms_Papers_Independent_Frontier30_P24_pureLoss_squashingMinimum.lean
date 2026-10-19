-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P24_pureLoss_squashingMinimum
-- name    : QAlgorithms.Papers.Independent.Frontier30.P24.pureLoss_squashingMinimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:38:12.675005+00:00
-- url     : https://prove2.me/theorems/b3e58f51-0a31-4197-bc61-7f912f49ff20
-- title:
--   Symmetric convex minimization of the pure-loss test bound
-- statement:
--   Let $0\le\eta\le1$ be a transmissivity and let $N\ge0$ be a finite mean-photon-number budget. Define the thermal entropy in bits by $g(x)=((x+1)\log(x+1)-x\log x)/\log2$, with $0\log0=0$. For $s\in[0,1]$, let
--
--   $$
--   F_{\eta,N}(s)=\frac12\bigl[g((1-s+\eta s)N)+g((s+\eta(1-s))N)-g(s(1-\eta)N)-g((1-s)(1-\eta)N)\bigr].
--   $$
--
--   The function $F_{\eta,N}$ is convex on $[0,1]$ and satisfies $F_{\eta,N}(s)=F_{\eta,N}(1-s)$ there. Its minimum is attained at $s=1/2$, and
--
--   $$
--   \min_{s\in[0,1]}F_{\eta,N}(s)=F_{\eta,N}(1/2)=g((1+\eta)N/2)-g((1-\eta)N/2).
--   $$
--
--   This identifies the best scalar value within the particular family of pure-loss test squashers. The assertion includes $N=0$, $\eta=0$, and $\eta=1$.
-- source:
--   The squashed entanglement of a quantum channel, arXiv:1310.0129v3, PDF p. 16, Section 6.1 after Eq.(26); Appendix A.1

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P24

open Filter

/-- PDF p.16 following Eq.(26), p.20 Eqs.(41)--(42), and Appendix A.1,
PDF pp.21--23: symmetry, convexity, and attained minimum of the displayed
scalar expression, for every physical transmissivity and finite energy budget.
Both the half-squashing witness and the simplified minimum value are retained.
The endpoint cases require no differentiation; no derivative formula with a
missing base-conversion factor is transcribed. -/
theorem pureLoss_squashingMinimum
    (eta photonNumber : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hphotonNumber : 0 ≤ photonNumber) :
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      pureLossSquashingBound eta photonNumber s =
        pureLossSquashingBound eta photonNumber (1 - s)) ∧
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (pureLossSquashingBound eta photonNumber) ∧
    IsLeast ((pureLossSquashingBound eta photonNumber) '' Set.Icc (0 : ℝ) 1)
      (pureLossSymmetricBound eta photonNumber) ∧
    pureLossSquashingBound eta photonNumber (1 / 2) =
      pureLossSymmetricBound eta photonNumber := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P24

end
