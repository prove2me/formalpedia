-- Prove2me | Theorems.Thm_OtterAMM_TwoSided_eqs_21_22
-- name    : OtterAMM.TwoSided.eqs_21_22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:48:05.992193+00:00
-- url     : https://prove2.me/theorems/366138f1-5746-4631-aacd-d66ad2776229
-- title:
--   §6.3.1, Eqs. (21)–(22) — the truthful utility of a real sell-Y user in Otter
-- statement:
--   Let $F$ satisfy (A1)–(A4) and the selection rule be admissible. Fix the other identities $O$ with reports in $\mathbb R^2_{\ge0}$ and a real sell-Y user of type $(v,q)\in\mathbb R^2_{\ge0}$ reporting truthfully under a fresh identity. Let $D^{oth}_Y=D_Y(O)$, $D^{oth}_X=D_X(O)$, $M^{oth}_Y=\rho_0D^{oth}_X$, $\ell=(M^{oth}_Y-D^{oth}_Y)_+$, and $\phi_Y$ be taken over the other sell-Y reports. Then the truthful utility $\mathrm{Util}_{tr}$ satisfies:
--
--   - if $v>\sigma_0$: $\mathrm{Util}_{tr}=0$;
--   - if $v\le\sigma_0$ and $D^{oth}_Y+q<M^{oth}_Y$: $\mathrm{Util}_{tr}=(\sigma_0-v)q$ and $\phi_Y(M^{oth}_Y;v,q)=(\sigma_0-v)q$ (21);
--   - if $v\le\sigma_0$ and $D^{oth}_Y+q\ge M^{oth}_Y$: $\mathrm{Util}_{tr}=\phi_Y(M^{oth}_Y;v,q)\ge(\sigma_0-v)\ell$ (22).
--
--   Differences from the source:
--   - reading: allocation: among welfare maximizers choose one maximizing total sold, then an arbitrary exogenous tie-breaking rule → the statement holds for every selection rule sel with SelRule.Admissible (on every one-sided curve and every finite bid set with nonnegative reports it returns a welfare maximizer of largest total); sel may depend on identity labels; reason: an 'arbitrary exogenous tie-breaking rule' is any choice among the max-total maximizers; such rules exist (continuous welfare on a compact box), so the hypothesis is not vacuous; the §4 priority rule is one instance
--   - encoding: utility Eq. (2) with value −∞ → util in EReal, −∞ = ⊥; no EReal arithmetic is performed; reason: keeps −∞ a genuine outcome, never a junk real value
--   - encoding: F : (−b_y, +∞) → (−∞, x0) → F : ℝ → ℝ inside the structure PricingCurve, every assumption (A1)–(A4) and the codomain bound imposed on (−b, +∞) only; H(x) = −F⁻¹(−x) through Function.invFunOn on (−b, +∞); reason: Lean functions are total; values outside the domain are never used, so no instance changes
--   - encoding: identities, the block and its reports → identities are labels in ℕ, a block is a Finset of labels with a report function rep (an ordered block is a List of labels); reason: a finite set of identities with reports is exactly such a pair; labels are never compared by the mechanism except through the selection rule
--   - encoding: reports and types are in ℝ²≥0 (§2) → nonnegativity of asks and budgets is a hypothesis on the identities that occur (ValidOn); reason: the paper's domain of reports, not an extra condition
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), p. 23, §6.3.1, Eqs. (21)–(22) (PDF 25)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_VCG
import Definitions.Def_OtterAMM_TwoSided_Otter

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- §6.3.1, Eqs. (21)–(22) (p. 23): the truthful utility of a real sell-Y user of type
`(v, q)` in Otter, given the other identities `O` with reports `rep`;
`D^oth_Y = D_Y(O)`, `M^oth_Y = ρ0·D_X(O)`, `ℓ = (M^oth_Y − D^oth_Y)_+`, and
`ϕ_Y(M; v, q)` is taken over the other sell-Y reports. -/
theorem eqs_21_22 (C : PricingCurve) (sel : SelRule) (hsel : sel.Admissible)
    (O : Finset Ident) (rep : Ident → Report) (hO : ValidOn O rep) (i0 : Ident) (hi0 : i0 ∉ O)
    (v q : ℝ) (hv : 0 ≤ v) (hq : 0 ≤ q) :
    (C.σ0 < v →
      util ⟨Dir.sellY, v, q⟩ (Function.update rep i0 ⟨Dir.sellY, v, q⟩)
        (otter C sel (insert i0 O) (Function.update rep i0 ⟨Dir.sellY, v, q⟩)) {i0} = 0) ∧
    (v ≤ C.σ0 → DY C O rep + q < C.ρ0 * DX C O rep →
      util ⟨Dir.sellY, v, q⟩ (Function.update rep i0 ⟨Dir.sellY, v, q⟩)
          (otter C sel (insert i0 O) (Function.update rep i0 ⟨Dir.sellY, v, q⟩)) {i0} =
        (((C.σ0 - v) * q : ℝ) : EReal) ∧
      phiY C (sellYs O rep) (askOf rep) (budgetOf rep) i0 (C.ρ0 * DX C O rep) v q =
        (C.σ0 - v) * q) ∧
    (v ≤ C.σ0 → C.ρ0 * DX C O rep ≤ DY C O rep + q →
      util ⟨Dir.sellY, v, q⟩ (Function.update rep i0 ⟨Dir.sellY, v, q⟩)
          (otter C sel (insert i0 O) (Function.update rep i0 ⟨Dir.sellY, v, q⟩)) {i0} =
        ((phiY C (sellYs O rep) (askOf rep) (budgetOf rep) i0 (C.ρ0 * DX C O rep) v q : ℝ) :
          EReal) ∧
      (C.σ0 - v) * max (C.ρ0 * DX C O rep - DY C O rep) 0 ≤
        phiY C (sellYs O rep) (askOf rep) (budgetOf rep) i0 (C.ρ0 * DX C O rep) v q) := by sorry

end OtterAMM.TwoSided
