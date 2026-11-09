-- Prove2me | Theorems.Thm_QCSepTotal_theorem_4_1_minimax
-- name    : QCSepTotal.theorem_4_1_minimax
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:38:12.843264+00:00
-- url     : https://prove2.me/theorems/fc65bc28-9a82-468c-9641-7296ca3ab096
-- title:
--   Proof of Theorem 4.1, minimax argument — distributional protocols for all $\mu$ give one worst-case protocol
-- statement:
--   Let $F$ be a partial function on finite sets $X\times Y$, let $C\ge0$ be an integer and $\gamma$ real. Suppose that for every distribution $\mu$ supported on $\mathrm{dom}(F)$ there is a randomized protocol $\Pi_\mu$ with $CC(\Pi_\mu)\le C$ and $\mathrm{err}_\mu(\Pi_\mu)\le\gamma$. Then there is a randomized protocol $\tilde\Pi$ with
--   $$CC(\tilde\Pi)\le C,\qquad \Pr[\tilde\Pi(x,y)\neq F(x,y)]\le\gamma\ \text{ for every }(x,y)\in\mathrm{dom}(F).$$
--
--   In the proof of Theorem 4.1 it is applied with $C=CC(\Pi)+1$ and $\gamma=\frac12-\frac\delta3$.
--
--   Differences from the source:
--   - generalization: inputs in {0,1}^n → arbitrary finite input types X, Y; reason: {0,1}^n is a finite type, so the statement specializes
--   - generalization: cost bound CC(Π) + 1 and error 1/2 − δ/3 → any cost bound C and any error level γ; reason: the minimax principle holds for every C and γ; the printed values are a special case
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), proof of Theorem 4.1, "Minimax argument", p.10

import Mathlib
import Definitions.Def_QCSepTotal_RandProtocol

namespace QCSepTotal

/-- **Proof of Theorem 4.1, minimax argument** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.10). For every `µ` on
`dom(F)` we have a protocol `Π_µ` with `CC(Π_µ) ≤ CC(Π) + 1` and `err_µ(Π_µ) ≤ 1/2 − δ/3`; the
minimax principle gives one protocol `Π̃` for `F` with `CC(Π̃) ≤ CC(Π) + 1` and
`err(Π̃) ≤ 1/2 − δ/3`.

**Formalization Note.** Stated as the minimax principle used there, for any cost bound `C` (the
paper's `CC(Π) + 1`) and any error level `γ` (the paper's `1/2 − δ/3`): if every distribution
supported on `dom(F)` admits a protocol of cost at most `C` and distributional error at most `γ`,
then a single protocol of cost at most `C` has error at most `γ` on every promised input. -/
theorem theorem_4_1_minimax {X Y : Type} [Fintype X] [Fintype Y] (F : PartialFn X Y) (C : ℕ)
    (γ : ℝ)
    (h : ∀ μ : PMF (X × Y), (∀ p ∈ μ.support, (F p.1 p.2).isSome) →
      ∃ P : RandProtocol X Y, P.cost ≤ C ∧ P.distErr F μ ≤ γ) :
    ∃ P : RandProtocol X Y, P.cost ≤ C ∧ P.Computes F γ := by sorry

end QCSepTotal
