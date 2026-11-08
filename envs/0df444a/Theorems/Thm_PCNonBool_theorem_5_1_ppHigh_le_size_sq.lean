-- Prove2me | Theorems.Thm_PCNonBool_theorem_5_1_ppHigh_le_size_sq
-- name    : PCNonBool.theorem_5_1_ppHigh_le_size_sq
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:33:40.179188+00:00
-- url     : https://prove2.me/theorems/6a5b6f0e-f613-494b-a276-6e46bbb10864
-- title:
--   Proof of Theorem 5.1 — $|\mathrm{PPHigh}_D(\pi)| \le |\pi|^2$
-- statement:
--   **From the proof of Theorem 5.1.** For every finite sequence $\pi$ of polynomials in the variables of a bipartite graph $G$, every induced instance and every $D\in\mathbb R$,
--   $$|\mathrm{PPHigh}_D(\pi)|\ \le\ |\pi|^2,$$
--   where $|\pi|$ is the total number of monomials of the lines of $\pi$.
--
--   Combined with the geometric decrease of Lemma 5.14 this converts the pair count into the size lower bound of Theorem 5.1.
--
--   Differences from the source:
--   - generalization: π the refutation given to Algorithm 1, ppdeg in FPHP(G) → any finite sequence π, any instance (Ua, Va), any real D; reason: |PPHigh_D(π)| ≤ |Qset(π)| ≤ Σ_p |p|² ≤ |π|² holds for every sequence
--   - encoding: |π|, the size of π → pcSize π, the total number of monomials of the lines; reason: the paper's size measure (p.11)
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), proof of Theorem 5.1, p.32 (PDF p.35)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_pcSize
import Definitions.Def_PCNonBool_ppHighOn

namespace PCNonBool

/-- **Proof of Theorem 5.1**, "`|PPHigh_D(π)| ≤ |π|²`" (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.32 (PDF p.35)): the number of
monomial pairs of high pairwise pigeon degree in the lines of `π` is at most the square of the
size of `π`. Stated for every sequence, instance and threshold. -/
theorem theorem_5_1_ppHigh_le_size_sq {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (Ua : Finset U) (Va : Finset V) (D : ℝ)
    (π : List (MvPolynomial (Var G) F)) :
    (ppHighOn G Ua Va D π).card ≤ pcSize π ^ 2 := by sorry

end PCNonBool
