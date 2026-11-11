-- Prove2me | Theorems.Thm_RSVProductQLTC_ProductExpansion_claim_3_4
-- name    : RSVProductQLTC.ProductExpansion.claim_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:41.161937+00:00
-- url     : https://prove2.me/theorems/64e9af30-60d4-4164-9f52-1da052e678bc
-- title:
--   Claim 3.4 — dual of projective Reed–Solomon codes
-- statement:
--   Let $K=\mathbb F_s$ and $E$ be finite fields with a specified inclusion $K\hookrightarrow E$. Let $0\le d\le s-1$, and use the projective coordinates $r_x=(x,1)^{\mathsf T}$ and $r_\infty=(1,0)^{\mathsf T}$. With respect to the standard $E$-bilinear dot product on $E^{K\cup\{\infty\}}$,
--   $$\operatorname{PRS}_{d}(K;E)^\perp=\operatorname{PRS}_{s-1-d}(K;E).$$
--   This identifies the dual base codes required by the dual local constraint system. The endpoints $d=0$ and $d=s-1$ are both included; no restriction to prime fields or binary fields is made.
--
--   Differences from the source:
--   - encoding: finite subfield K contained in E → finite field types with a specified field homomorphism K to E; reason: field homomorphisms are injective; this represents every source inclusion
--   - encoding: projective evaluation of homogeneous polynomials → span of all d+1 evaluated homogeneous monomials on Option K; reason: arbitrary coefficients give exactly that span, with none representing infinity
-- source:
--   Mitali Bafna, Anqi Li, Quynh T. Nguyen, STOC 2027 submission #1136 (October 2026), Claim 3.4, printed p.8 (PDF p.9)

import Mathlib
import Definitions.Def_RSVProductQLTC_ProductExpansion_projectiveRS
set_option autoImplicit false

namespace RSVProductQLTC.ProductExpansion

/-- Bafna–Li–Nguyen, Claim 3.4, printed p.8 (PDF p.9). -/
theorem claim_3_4 {K E : Type} [Field K] [Fintype K] [Field E] [Fintype E]
    (ι : K →+* E) (d : ℕ) (hd : d ≤ Fintype.card K - 1) :
    GoodQLTC.dualCode (projectiveRS ι d) = projectiveRS ι (Fintype.card K - 1 - d) := by sorry

end RSVProductQLTC.ProductExpansion
