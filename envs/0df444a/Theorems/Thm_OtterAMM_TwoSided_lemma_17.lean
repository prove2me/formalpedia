-- Prove2me | Theorems.Thm_OtterAMM_TwoSided_lemma_17
-- name    : OtterAMM.TwoSided.lemma_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:48:00.960499+00:00
-- url     : https://prove2.me/theorems/61476c01-92d1-4a02-8a6a-2992f4be15c7
-- title:
--   Lemma 17 — curve-shift lemma: $\phi_Y(M+\alpha;v,\hat q)\le\phi_Y(M;v,q)+(\sigma_0-v)\alpha$ and its sell-X counterpart
-- statement:
--   Let $F$ satisfy (A1)–(A4). Fix a finite set $O$ of sell-Y reports (asks and budgets $\ge0$) other than one comparison seller, and for $M,q\ge0$ let $\phi_Y(M;v,q)=W_{\tilde F^M_Y}(O\cup\{(v,q)\})-W_{\tilde F^M_Y}(O)$. For every $v\le\sigma_0$, every $\alpha\ge0$ and every comparison cap $0\le\hat q\le q+\alpha$,
--   $$\phi_Y(M+\alpha;v,\hat q)\ \le\ \phi_Y(M;v,q)+(\sigma_0-v)\alpha.\qquad(19)$$
--   Symmetrically, for a finite set $O$ of sell-X reports and $\phi_X(M;u,r)=W_{\tilde H^M_X}(O\cup\{(u,r)\})-W_{\tilde H^M_X}(O)$: for $u\le\rho_0$, $\alpha\ge0$ and $0\le\hat r\le r+\alpha$, $\phi_X(M+\alpha;u,\hat r)\le\phi_X(M;u,r)+(\rho_0-u)\alpha$.
--
--   It bounds the gain a user can obtain by extending the spot segment with its own opposite-direction bids.
--
--   Differences from the source:
--   - encoding: (v, q) and (u, r) are reports, in ℝ²≥0 → hypotheses 0 ≤ v and 0 ≤ u (and 0 ≤ q, 0 ≤ r, 0 ≤ M as printed); reason: reports live in ℝ²≥0 (§2), so ϕ_Y, ϕ_X are defined for such pairs only
--   - encoding: O ∪ {(v, q)} with a comparison seller other than O → the comparison seller is a label i0 ∉ O with ask v and budget q (Function.update); reason: a fresh identity is exactly 'a seller other than O'
--   - encoding: Eq. (8): F̃^M_Y(y) = D_X + F(y − M) for y ≥ M (and H̃^M_X(x) = D_Y + H(x − M)) → curveY C M = spotExtend C.F σ0 M, i.e. σ0·M + F(y − M) (curveX: ρ0·M + H(x − M)); reason: with M = ρ0·D_X one has σ0·M = D_X exactly (σ0·ρ0 = 1), so the curve is the printed one
--   - encoding: F : (−b_y, +∞) → (−∞, x0) → F : ℝ → ℝ inside the structure PricingCurve, every assumption (A1)–(A4) and the codomain bound imposed on (−b, +∞) only; H(x) = −F⁻¹(−x) through Function.invFunOn on (−b, +∞); reason: Lean functions are total; values outside the domain are never used, so no instance changes
--   - encoding: W_F(S) = max over the box 0 ≤ y_i ≤ q̃_i (Eq. (3)) → W = sSup of the welfare over the box; reason: for a one-sided curve the welfare is continuous on a compact nonempty box, so the supremum is the attained maximum
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), p. 22, Lemma 17 (PDF 24)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_VCG
import Definitions.Def_OtterAMM_TwoSided_Otter

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- Lemma 17 (p. 22), the curve-shift lemma, Eq. (19) and its sell-X counterpart. -/
theorem lemma_17 (C : PricingCurve) :
    (∀ (O : Finset Ident) (a q : Ident → ℝ) (i0 : Ident), (∀ j ∈ O, 0 ≤ a j ∧ 0 ≤ q j) →
      i0 ∉ O → ∀ M v qq α qhat : ℝ, 0 ≤ M → 0 ≤ v → v ≤ C.σ0 → 0 ≤ qq → 0 ≤ α →
      0 ≤ qhat → qhat ≤ qq + α →
      phiY C O a q i0 (M + α) v qhat ≤ phiY C O a q i0 M v qq + (C.σ0 - v) * α) ∧
    (∀ (O : Finset Ident) (a q : Ident → ℝ) (i0 : Ident), (∀ j ∈ O, 0 ≤ a j ∧ 0 ≤ q j) →
      i0 ∉ O → ∀ M u r α rhat : ℝ, 0 ≤ M → 0 ≤ u → u ≤ C.ρ0 → 0 ≤ r → 0 ≤ α →
      0 ≤ rhat → rhat ≤ r + α →
      phiX C O a q i0 (M + α) u rhat ≤ phiX C O a q i0 M u r + (C.ρ0 - u) * α) := by sorry

end OtterAMM.TwoSided
