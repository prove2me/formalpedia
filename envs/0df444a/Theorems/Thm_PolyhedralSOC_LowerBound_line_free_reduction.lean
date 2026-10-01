-- Prove2me | Theorems.Thm_PolyhedralSOC_LowerBound_line_free_reduction
-- name    : PolyhedralSOC.LowerBound.line_free_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:46:31.556689+00:00
-- url     : https://prove2.me/theorems/7894c956-fc16-49d0-882e-9a5147d25758
-- title:
--   Proposition 3.1, proof — reduction to a cone $K$ without lines
-- statement:
--   Let $\varepsilon>0$ and let $\Pi:\mathbb R^k\times\mathbb R\times\mathbb R^p\to\mathbb R^q$ be a polyhedral $\varepsilon$-approximation of the Lorentz cone $L^k$. Then there are $p'\le p$ and a linear map $\Pi':\mathbb R^k\times\mathbb R\times\mathbb R^{p'}\to\mathbb R^q$, with the **same number $q$** of inequalities, such that
--   1. $\Pi'$ is again a polyhedral $\varepsilon$-approximation of $L^k$;
--   2. $\Pi$ and $\Pi'$ have the same projection onto the $(y,t)$-space:
--   $$\{(y,t)\mid \exists u\in\mathbb R^p:\ \Pi(y,t,u)\ge0\}=\{(y,t)\mid \exists u'\in\mathbb R^{p'}:\ \Pi'(y,t,u')\ge0\};$$
--   3. the cone $K'=\{(y,t,u')\mid \Pi'(y,t,u')\ge0\}$ contains no line.
--
--   In the paper this is the step "replacing, if necessary, $u$ with its projection on a properly chosen subspace in $\mathbb R^p$, we may assume that the cone $K$ itself does not contain lines"; it allows the rest of the proof to describe $K$ by its finitely many extreme rays.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 202, Proposition 3.1, proof (reduction to a line-free cone K)

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox
import Definitions.Def_PolyhedralSOC_LowerBound_ProofObjects

namespace PolyhedralSOC.LowerBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 3.1, proof, p. 202 (PDF p. 10):
"replacing, if necessary, u with its projection on a properly chosen subspace in R^p, we may
assume that the cone K itself does not contain lines". For `ε > 0`, every polyhedral
`ε`-approximation `Π` of `L^k` with `q` inequalities can be replaced by one, `Π'`, with the same
`q`, at most `p` auxiliary variables, the same projection onto the `(y, t)`-space, and a cone
`K' = {Π' ≥ 0}` that contains no line. -/
theorem line_free_reduction {k p q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ))
    (hP : Shared.IsPolyhedralApprox k p q ε P) :
    ∃ (p' : ℕ) (P' : (Fin k → ℝ) × ℝ × (Fin p' → ℝ) →ₗ[ℝ] (Fin q → ℝ)),
      p' ≤ p ∧ Shared.IsPolyhedralApprox k p' q ε P' ∧
      (∀ (y : Fin k → ℝ) (t : ℝ),
        (∃ u : Fin p → ℝ, 0 ≤ P (y, t, u)) ↔ (∃ u' : Fin p' → ℝ, 0 ≤ P' (y, t, u'))) ∧
      IsLineFree P' := by sorry

end PolyhedralSOC.LowerBound
