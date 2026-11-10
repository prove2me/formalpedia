-- Prove2me | Theorems.Thm_OtterAMM_TwoSided_section_6_3_2
-- name    : OtterAMM.TwoSided.section_6_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:48:04.715204+00:00
-- url     : https://prove2.me/theorems/1aa73c10-dad3-412e-a58b-bf2d2805dd6b
-- title:
--   §6.3.2 — no finite cross-direction sybil attack benefits a real sell-X user
-- statement:
--   Let $F$ satisfy (A1)–(A4) and the selection rule be admissible. Fix the other identities $O$ with arbitrary reports in $\mathbb R^2_{\ge0}$, and a real sell-X user of type $(u,r)\in\mathbb R^2_{\ge0}$. Replace its truthful identity by an arbitrary finite, possibly empty, set $D$ of fresh identities with arbitrary reports in $\mathbb R^2_{\ge0}$ in either direction. Then its utility (2), computed from the aggregate flows of $D$ in the Otter outcome of $D\cup O$, is at most its utility from one truthful identity:
--   $$\mathrm{Util}(D)\ \le\ \mathrm{Util}_{tr}.$$
--   Together with §6.3.1 this is the UIC clause of Theorem 10.
--
--   Differences from the source:
--   - reading: allocation: among welfare maximizers choose one maximizing total sold, then an arbitrary exogenous tie-breaking rule → the statement holds for every selection rule sel with SelRule.Admissible (on every one-sided curve and every finite bid set with nonnegative reports it returns a welfare maximizer of largest total); sel may depend on identity labels; reason: an 'arbitrary exogenous tie-breaking rule' is any choice among the max-total maximizers; such rules exist (continuous welfare on a compact box), so the hypothesis is not vacuous; the §4 priority rule is one instance
--   - encoding: utility Eq. (2) with value −∞ → util in EReal, −∞ = ⊥; no EReal arithmetic is performed; reason: keeps −∞ a genuine outcome, never a junk real value
--   - encoding: F : (−b_y, +∞) → (−∞, x0) → F : ℝ → ℝ inside the structure PricingCurve, every assumption (A1)–(A4) and the codomain bound imposed on (−b, +∞) only; H(x) = −F⁻¹(−x) through Function.invFunOn on (−b, +∞); reason: Lean functions are total; values outside the domain are never used, so no instance changes
--   - encoding: identities, the block and its reports → identities are labels in ℕ, a block is a Finset of labels with a report function rep (an ordered block is a List of labels); reason: a finite set of identities with reports is exactly such a pair; labels are never compared by the mechanism except through the selection rule
--   - encoding: reports and types are in ℝ²≥0 (§2) → nonnegativity of asks and budgets is a hypothesis on the identities that occur (ValidOn); reason: the paper's domain of reports, not an extra condition
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), pp. 24–25, §6.3.2 (PDF 26–27)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_VCG
import Definitions.Def_OtterAMM_TwoSided_Otter

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- §6.3.2 (pp. 24–25): no finite set of identities with arbitrary reports in either direction
benefits a real sell-X user of type `(u, r)` in Otter: its Eq. (2) utility is at
most that of one truthful identity, whatever the other identities report. -/
theorem section_6_3_2 (C : PricingCurve) (sel : SelRule) (hsel : sel.Admissible)
    (O : Finset Ident) (rep : Ident → Report) (u r : ℝ) (i0 : Ident) (D : Finset Ident)
    (dev : Ident → Report)
    (hO : ValidOn O rep) (hu : 0 ≤ u) (hr : 0 ≤ r) (hi0 : i0 ∉ O) (hD : Disjoint D O)
    (hdev : ValidOn D dev) :
    util ⟨Dir.sellX, u, r⟩ (overlay D dev rep) (otter C sel (D ∪ O) (overlay D dev rep)) D ≤
      util ⟨Dir.sellX, u, r⟩ (Function.update rep i0 ⟨Dir.sellX, u, r⟩)
        (otter C sel (insert i0 O) (Function.update rep i0 ⟨Dir.sellX, u, r⟩)) {i0} := by sorry

end OtterAMM.TwoSided
