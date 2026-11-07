-- Prove2me | Theorems.Thm_PCNonBool_lemma_5_9
-- name    : PCNonBool.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:41.423041+00:00
-- url     : https://prove2.me/theorems/4e7b8454-20e3-404b-b1bf-24d8576974cf
-- title:
--   Lemma 5.9 — PigeonSplit maps a derivation from $P$ to a derivation from PigeonSplit$(P)$
-- statement:
--   **Lemma 5.9.** Let $\mathbb F$ be a field of characteristic different from $2$ and $P$ a set of polynomials in the variables $\{x_{i,j}\}$ of a bipartite graph $G$. If $\pi$ is a polynomial calculus derivation of a polynomial $p_\tau$ from $P$, then for every pigeon $i$ and holes $j\ne j'\in N(i)$, the sequence $\mathrm{PigeonSplit}_{i,j,j'}(\pi)$ is a polynomial calculus derivation of $\mathrm{PigeonSplit}_{i,j,j'}(p_\tau)$ from $\mathrm{PigeonSplit}_{i,j,j'}(P)$.
--
--   This is why splitting a refutation of FPHP$(G)$ yields a refutation of the split formula, the first step of Lemma 5.13.
--
--   Differences from the source:
--   - encoding: "a derivation of PigeonSplit_{i,j,j′}(p_τ)" → IsDerivation of splitSeq π; its last two lines are PigeonSplit(p_τ) by the definition of splitSeq; reason: PigeonSplit of a sequence is the concatenation of the split lines
--   - generalization: P a set of polynomials in the variables {x_{i,j}} → any set P of polynomials in the edge variables of G; reason: same objects; P is arbitrary in the source too
--   - reading: no field characteristic stated in the lemma; PigeonSplit (37) divides by 2 → ringChar F ≠ 2; reason: Section 5 works over fields of characteristic different from 2 (Theorem 5.1, p.26), which Definition 5.8's factor 1/2 presupposes
--   - reading: polynomial calculus (refutations on both sides of the statement) → the mission's PC model on both sides: lines reduced modulo the range axioms, axiom lines c·red(a) with c ∈ F, fan-in 2, refutation = derivation containing 1; reason: one PC model is used throughout the mission; it is the model the paper's own splitting and restriction steps (Lemmas 5.9, 5.13) need
--   - encoding: lines of a refutation represented in the quotient ring modulo the range axioms (p.11); size = number of monomials → lines are the multilinear representatives (redPM / redBool normal forms); the multiplication rule reduces its result; size counts their monomials; reason: the paper's own convention (p.11); it only strengthens size and degree lower bounds
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Lemma 5.9, p.28 (PDF p.31)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_redPM
import Definitions.Def_PCNonBool_IsDerivation
import Definitions.Def_PCNonBool_splitSeq
import Definitions.Def_PCNonBool_splitSet

namespace PCNonBool

/-- **Lemma 5.9** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.28 (PDF p.31)). If `π` is a polynomial calculus derivation from `P`,
then for all `i ∈ U` and `j ≠ j' ∈ N(i)`, `PigeonSplit_{i,j,j'}(π)` is a polynomial calculus
derivation from `PigeonSplit_{i,j,j'}(P)`; its last two lines are `PigeonSplit_{i,j,j'}(p_τ)`.

**Formalization Note** Derivations are in the mission's PC model (lines reduced modulo `x² - 1`,
fan-in 2, scalar-multiple axiom lines). A multiplication by `x_{i,j}` is mapped to the two lines
`(-q₂, -q₁)`, linear combinations of earlier split lines. -/
theorem lemma_5_9 {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] (hF : ringChar F ≠ 2)
    (G : BipGraph U V) (P : Set (MvPolynomial (Var G) F)) (π : List (MvPolynomial (Var G) F))
    (hπ : IsDerivation redPM P π) (i : U) (j j' : V) (hj : G.Adj i j) (hj' : G.Adj i j')
    (hjj : j ≠ j') :
    IsDerivation redPM (splitSet G i j j' P) (splitSeq G i j j' π) := by sorry

end PCNonBool
