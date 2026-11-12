-- Prove2me | Theorems.Thm_PoQHierarchy_Main_lemma_5_7
-- name    : PoQHierarchy.Main.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:52:23.274806+00:00
-- url     : https://prove2.me/theorems/cb1809ff-1573-45dd-a4c8-aebb7ca9ad43
-- title:
--   Lemma 5.7 — operational non-signaling algebraic sequential correlations equal $I$-quantum commuting operator correlations
-- statement:
--   Fix $n$, finite question and answer sets and $I\subseteq[n]$. The set of correlations
--   $$\Pr[a\mid x]=\phi\circ T^{(1)}_{a_1|x_1}\circ\cdots\circ T^{(n)}_{a_n|x_n}(1)$$
--   realizable by operational non-signaling $n$-partite $I$-quantum algebraic sequential strategies (Definition 5.6) is identical to the set of correlations
--   $$\Pr[a\mid x]=\langle\Omega|\textstyle\prod_{i=1}^nP^{(i)}_{x_ia_i}|\Omega\rangle$$
--   realizable by $I$-quantum commuting operator strategies (Definition 5.1). Both inclusions are asserted.
--
--   This algebraic characterization is what lets the limit of a prover's sequential behaviour, taken on the universal algebra of sequential measurements, be read back as an $I$-quantum commuting operator strategy.
--
--   Differences from the source:
--   - encoding: players [n] and finite question/answer sets I_i, O_i → Fin n, Fin (q i), Fin (o i); reason: every finite set is in bijection with some Fin m; values and correlations are unchanged
--   - encoding: possibly infinite-dimensional Hilbert space H → any complex Hilbert space in Lean's lowest universe, with bounded operators; reason: the finitely many operators of a strategy generate a separable cyclic subspace, so no correlation is lost
--   - encoding: real-valued correlations → complex-valued correlations ϕ(…) and ⟨Ω, ∏P Ω⟩ compared as complex functions; reason: both are real; comparing complex values asserts at least the real equality
--   - encoding: C*-algebras and CP maps → Mathlib CStarAlgebra with its C*-order as a star-ordered partial order, and Mathlib's completely positive maps; reason: the star-ordered order on a C*-algebra is its positive cone; algebras in Lean's lowest universe suffice for both constructions
--   - generalization: n-partite strategies for an n-player game, n ≥ 2 (§3.2, p.19; §5.1 preamble) → any number n of players (no hypothesis 2 ≤ n); reason: the Lean statement covers more games; restricted to n ≥ 2 it is exactly the source's statement
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), p.31, Lemma 5.7; canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_AlgSeq
import Definitions.Def_PoQHierarchy_Main_ICO

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-- Lemma 5.7, p.31: the correlations realizable by operational non-signaling `n`-partite
`I`-quantum algebraic sequential strategies are exactly the correlations realizable by `I`-quantum
commuting operator strategies. -/
theorem lemma_5_7 (n : ℕ) (q o : Fin n → ℕ) (I : Finset (Fin n)) :
    {p | ∃ St : AlgSeqStrategy n q o I, St.OperationalNS ∧ St.corr = p} =
      {p | ∃ S : ICOStrategy n q o I, S.corr = p} := by sorry

end PoQHierarchy.Main
