-- Prove2me | Theorems.Thm_RobustQSC_proposition_14
-- name    : RobustQSC.proposition_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:20.633214+00:00
-- url     : https://prove2.me/theorems/15fee8c2-dd6e-4ff6-88c4-74ac276e672f
-- title:
--   Proposition 14, p.50 — extension under local escape, $C_\alpha\le1100/\alpha^3$
-- statement:
--   Let $A\subseteq\{0,1\}^n$ have the local escape property with parameter $\alpha$. Then
--
--   $$
--   \mathrm{Inf}_{\mathrm{unif}}(\mathrm{Ext}_Ah)\le C_\alpha\,\mathrm{Inf}^{\mathrm{int}(A)}_{\mathrm{unif}}(h)\qquad\forall h:A\to\mathbb C,
--   $$
--
--   and one may take $C_\alpha\le1100/\alpha^3$ provided $\alpha<1$. This is deterministic.
--
--   The constant depends on $\alpha$ only. The extension brings the standard low-degree counting of low-influence functions on the uniform cube to functions on $A$.
--
--   Differences from the source:
--   - encoding: $h:A\to\mathbb C$ → $h$ on the whole cube; reason: both sides read $h$ on $A$ only; the paper itself defines $\mathrm{Ext}_A$ "for any $h:\{0,1\}^n\to\mathbb C$"
--   - encoding: "we may take $C_\alpha\le1100/\alpha^3$" → the inequality with the constant $1100/\alpha^3$ for $\alpha<1$, plus the existence of $C_\alpha$ for every $\alpha>0$; reason: the two clauses of the statement; $C_\alpha$ is chosen before $n$ and $A$
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Proposition 14, p.50; Ext_A, p.48; local escape, Proposition 13, p.49

import Definitions.Def_RobustQSC_LocalEscape
import Definitions.Def_RobustQSC_extA
import Definitions.Def_RobustQSC_infMu

namespace RobustQSC

open QAlgorithms

/-- **Proposition 14 (Extension under local escape).** Let `A ⊆ {0,1}ⁿ` with the local escape
property with parameter `α`. Then `Inf_unif(Ext_A h) ≤ C_α Inf^{int(A)}_unif(h)` for all
`h : A → ℂ`, and one may take `C_α ≤ 1100/α³` provided `α < 1`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Proposition 14, p.50; `Ext_A`, p.48; local escape, Proposition 13, p.49.

**Formalization Note.** `C_α` depends on `α` only (not on `n` or `A`). `h : A → ℂ` is taken as a
function on the whole cube; both sides read `h` on `A` only. -/
theorem proposition_14 :
    (∀ α : ℝ, 0 < α → ∃ Cα : ℝ, ∀ (n : ℕ) (A : Set (Qubits n)), LocalEscape A α →
      ∀ h : Qubits n → ℂ, infUnif (extA A h) ≤ Cα * infIntUnif A h) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∀ (n : ℕ) (A : Set (Qubits n)), LocalEscape A α →
      ∀ h : Qubits n → ℂ, infUnif (extA A h) ≤ 1100 / α ^ 3 * infIntUnif A h) := by sorry

end RobustQSC
