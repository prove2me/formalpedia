-- Prove2me | Theorems.Thm_SteinerAPX_theorem_1
-- name    : SteinerAPX.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:33.694084+00:00
-- url     : https://prove2.me/theorems/aa544dc9-5048-4e45-ad33-daa2f5bf233b
-- title:
--   Theorem 1 — Euclidean Steiner Tree is APX-hard in $O(\log n)$ dimensions
-- statement:
--   There are constants $C>0$ and $\beta>0$ such that the following two statements hold.
--
--   **(A) Constant gap in logarithmic dimension.** Every language $\mathcal L$ in NP has a polynomial-time reduction mapping each word $x$ to $n\ge2$ distinct rational terminals $P_x\subseteq\mathbb R^k$ with
--   $$
--   k\le C\log n
--   $$
--   and a rational threshold $\tau_x>0$ such that
--   $$
--   x\in\mathcal L\ \Longrightarrow\ \mathrm{OPT}(P_x)\le\tau_x,\qquad
--   x\notin\mathcal L\ \Longrightarrow\ \mathrm{OPT}(P_x)\ge(1+2\beta)\,\tau_x .
--   $$
--
--   **(B) No $(1+\beta)$-approximation unless P = NP.** If some polynomial-time algorithm outputs, on every set of $n\ge2$ distinct rational terminals in dimension $k\le C\log n$, a network spanning them of length at most $(1+\beta)\,\mathrm{OPT}$, then $\mathrm P=\mathrm{NP}$. The same holds for an algorithm that outputs a rational value $v$ with $\mathrm{OPT}\le v\le(1+\beta)\,\mathrm{OPT}$.
--
--   In particular Euclidean Steiner Tree has no PTAS in arbitrary dimension unless $\mathrm P=\mathrm{NP}$, answering Arora's question.
--
--   **Formalization Note** NP is the published verifier class `CookLevin.InNP` and $\mathrm P=\mathrm{NP}$ the published `PEqualsNP`; reductions and algorithms are Mathlib `TM2ComputableInPolyTime` machines with finite alphabets. $C$ and $\beta$ are fixed before the language. $\log$ is the natural logarithm. $\mathrm{OPT}$ is the infimum over spanning networks with free Steiner points.
--
--   Differences from the source:
--   - reading: Euclidean Steiner Tree is APX-hard in O(log n) dimensions → (A) a constant (1 + 2β) gap by a polynomial-time reduction from every NP language to rational instances with n ≥ 2 points in dimension k ≤ C·log n, and (B) no polynomial-time (1 + β)-approximation on that class, outputting a network or a value, unless P = NP; reason: the paper does not define APX-hardness; its proof (p.22) ends with a constant approximation gap in O(log n) dimensions and the next sentence after Theorem 1 draws "no PTAS unless P = NP"; the PTAS-reduction sense is not what the paper proves
--   - encoding: n terminals in ℝ^d with d = O(log n) → a valid raw rational terminal set with n ≥ 2 distinct points and k ≤ C·log n (natural logarithm), one C for all languages; reason: every coordinate on the paper's route is rational; n ≥ 2 makes log n positive; distinct points keep n the number of terminals
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Theorem 1, p.2 (PDF p.4); proof of Theorem 1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_SteinerAPX_RawTerminals
import Definitions.Def_SteinerAPX_NetworkApproximation

namespace SteinerAPX

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Theorem 1 (Euclidean Steiner Tree is APX-hard in `O(log n)` dimensions).** S. Bartlmae,
*Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission (manuscript sha256
6f78a9ea…), Theorem 1, p.2 (PDF p.4): "Theorem 1. Euclidean Steiner Tree is APX-hard in O(log n)
dimensions. This rules out a PTAS in arbitrary dimension unless P = NP, answering Arora's
question." Proof, p.22: "Thus the reduction preserves a constant approximation gap in O(log n)
dimensions, proving the theorem."

There are constants `C > 0` and `β > 0` such that:

(A) every language `L` in NP has a polynomial-time reduction mapping each word `x` to `n ≥ 2`
distinct rational points in `ℝᵏ` with `k ≤ C · log n` and a rational threshold `τ > 0`, with
`OPT ≤ τ` when `x ∈ L` and `OPT ≥ (1 + 2β)τ` when `x ∉ L`;

(B) if a polynomial-time algorithm outputs, on every such point set (`n ≥ 2` distinct rational
points, `k ≤ C · log n`), a spanning network of length at most `(1 + β) · OPT`, then P = NP; and if a
polynomial-time algorithm outputs a rational `v` with `OPT ≤ v ≤ (1 + β) · OPT` on every such point
set, then P = NP.

**Formalization Note** "APX-hard" is read as the paper's proof establishes it: a constant-factor
gap by a polynomial-time reduction from every NP language (A), and its consequence that no
polynomial-time `(1 + β)`-approximation exists unless P = NP (B), both for the network and for the
value output. `C` and `β` are chosen before the language. NP is the published verifier class
`CookLevin.InNP` and P = NP the published `PEqualsNP` (Mathlib `TM2ComputableInPolyTime` machines
with finite alphabets). `log` is the natural logarithm. Instances are raw rational terminal sets
(`RawTerminals`, `InClass`); `OPT` is `opt`, the infimum over spanning segment networks with free
Steiner points. -/
theorem theorem_1 :
    ∃ C β : ℝ, 0 < C ∧ 0 < β ∧
      (∀ L : BitLanguage, CookLevin.InNP L →
        ∃ construct : List Bool → RawInstance,
        ∃ comp : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) rawInstanceBits
            construct,
          MachineFiniteAlphabet.FiniteAlphabet comp.tm ∧
          ∀ x : List Bool,
            (construct x).1.InClass C ∧ (0 : ℝ) < ((construct x).2 : ℝ) ∧
            (L x → opt (construct x).1.terminals ≤ ((construct x).2 : ℝ)) ∧
            (¬ L x → (1 + 2 * β) * ((construct x).2 : ℝ) ≤ opt (construct x).1.terminals)) ∧
      (NetworkApproximation C β → PEqualsNP) ∧
      (ValueApproximation C β → PEqualsNP) := by sorry

end SteinerAPX
