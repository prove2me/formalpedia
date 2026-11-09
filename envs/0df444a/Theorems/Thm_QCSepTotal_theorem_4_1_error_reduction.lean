-- Prove2me | Theorems.Thm_QCSepTotal_theorem_4_1_error_reduction
-- name    : QCSepTotal.theorem_4_1_error_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:38:21.460903+00:00
-- url     : https://prove2.me/theorems/11d7b6f7-d2c5-4996-b4eb-bf2087b38dfb
-- title:
--   Proof of Theorem 4.1, error reduction — $CC(\Pi')\le K\,CC(\tilde\Pi)/\gamma^2$
-- statement:
--   There is an absolute constant $K$ with the following property. Let $F$ be a partial function on finite sets $X\times Y$, let $0<\gamma\le1/2$, and let $\tilde\Pi$ be a randomized protocol with $\Pr[\tilde\Pi(x,y)\neq F(x,y)]\le\frac12-\gamma$ for every $(x,y)\in\mathrm{dom}(F)$. Then there is a randomized protocol $\Pi'$ computing $F$ with error at most $1/3$ and
--   $$CC(\Pi')\le K\,\frac{CC(\tilde\Pi)}{\gamma^2}.$$
--
--   This is error reduction by independent repetition and majority voting. With $\gamma=\delta/3$ and $CC(\tilde\Pi)\le CC(\Pi)+1$ it gives the printed bound $CC(\Pi')\le O(\delta^{-2}(CC(\Pi)+1))$.
--
--   Differences from the source:
--   - generalization: inputs in {0,1}^n → arbitrary finite input types X, Y; reason: {0,1}^n is a finite type, so the statement specializes
--   - generalization: Π̃ from the minimax step, with advantage δ/3 and CC(Π̃) ≤ CC(Π) + 1; bound O(δ⁻²(CC(Π) + 1)) → any Π̃ with error at most 1/2 − γ, γ ∈ (0, 1/2]; bound K · CC(Π̃)/γ² with K absolute; reason: with γ = δ/3 and CC(Π̃) ≤ CC(Π) + 1 this is the printed bound
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), proof of Theorem 4.1, "Minimax argument", error reduction, p.10

import Mathlib
import Definitions.Def_QCSepTotal_RandProtocol

namespace QCSepTotal

/-- **Proof of Theorem 4.1, error reduction** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.10). Error reduction
by independent repetition and majority voting gives, from a protocol `Π̃` with
`err(Π̃) ≤ 1/2 − δ/3`, a `1/3`-error protocol `Π′` with
`CC(Π′) ≤ O(δ⁻²(CC(Π) + 1)) = O(c² CC(Π))`.

**Formalization Note.** Stated for any advantage `γ ∈ (0, 1/2]` (the paper's `δ/3`) and any
protocol `Π̃` with error at most `1/2 − γ` on every promised input: `CC(Π′) ≤ K · CC(Π̃)/γ²` with
an absolute constant `K` chosen first. With `CC(Π̃) ≤ CC(Π) + 1` this is the printed bound. -/
theorem theorem_4_1_error_reduction :
    ∃ K : ℝ, ∀ (X Y : Type) [Fintype X] [Fintype Y] (F : PartialFn X Y) (γ : ℝ), 0 < γ → γ ≤ 1 / 2 →
      ∀ P : RandProtocol X Y, P.Computes F (1 / 2 - γ) →
        ∃ P' : RandProtocol X Y, P'.Computes F (1 / 3) ∧ (P'.cost : ℝ) ≤ K * P.cost / γ ^ 2 := by sorry

end QCSepTotal
