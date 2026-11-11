-- Prove2me | Theorems.Thm_RSVProductQLTC_ProductExpansion_claim_3_5
-- name    : RSVProductQLTC.ProductExpansion.claim_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:48.381033+00:00
-- url     : https://prove2.me/theorems/3b76f163-534b-4ae0-9e26-6a5209def21d
-- title:
--   Claim 3.5 — Möbius symmetry
-- statement:
--   Let $K=\mathbb F_s$ and $E$ be finite fields with a specified inclusion $\iota:K\hookrightarrow E$. Fix $0\le d\le s-1$ and $B\in\mathrm{GL}_2(K)$. Define $\beta_B$ and $\lambda_B$ using $B r_x=\lambda_B(x)r_{\beta_B(x)}$ for every projective coordinate $x$, including poles and infinity. Then
--   $$\left\{\bigl(\iota(\lambda_B(x))^d\,u_{\beta_B(x)}\bigr)_x:u\in\operatorname{PRS}_d(K;E)\right\}=\operatorname{PRS}_d(K;E).$$
--   This is equality of the scaled image and the code. It supplies the symmetry needed when coordinates are transported across edges with different labels; permutation without the scale is not asserted.
--
--   Differences from the source:
--   - encoding: an element of GL2(K) → a 2 by 2 matrix with unit determinant; reason: equivalent invertibility over the field; the map covers all such matrices
--   - encoding: field inclusion and homogeneous projective evaluations → a field homomorphism and the span of evaluated homogeneous monomials on Option K; reason: represents the same inclusion, infinity coordinate, and polynomial code
-- source:
--   Mitali Bafna, Anqi Li, Quynh T. Nguyen, STOC 2027 submission #1136 (October 2026), Claim 3.5, printed p.9 (PDF p.10); degree and field conventions from §3.2, printed p.8 (PDF p.9)

import Mathlib
import Definitions.Def_RSVProductQLTC_ProductExpansion_projectiveRS
import Definitions.Def_RSVProductQLTC_ProductExpansion_mobius
set_option autoImplicit false

namespace RSVProductQLTC.ProductExpansion

/-- Bafna–Li–Nguyen, Claim 3.5, printed p.9 (PDF p.10). -/
theorem claim_3_5 {K E : Type} [Field K] [Fintype K] [Field E] [Fintype E]
    (ι : K →+* E) (d : ℕ) (hd : d ≤ Fintype.card K - 1)
    (B : Matrix (Fin 2) (Fin 2) K) (hB : IsUnit B.det) :
    (fun u : ProjectiveLine K → E => fun a =>
      ι (mobiusScale B a) ^ d * u (mobiusLabel B a)) ''
        (projectiveRS ι d : Set (ProjectiveLine K → E)) =
          (projectiveRS ι d : Set (ProjectiveLine K → E)) := by sorry

end RSVProductQLTC.ProductExpansion
