-- Prove2me | Theorems.Thm_PermDiameter_Binary_theorem_1_1
-- name    : PermDiameter.Binary.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:11:31.162763+00:00
-- url     : https://prove2.me/theorems/cf07f13a-df64-4c7e-ac8d-c1b74ed7485e
-- title:
--   Theorem 1.1 (Binary Diameter) — deciding $\operatorname{diam}(\langle\Sigma\rangle,\Sigma)\le k$ with $k$ in binary is PSPACE-complete, hard already for symmetric $\Sigma$
-- statement:
--   **Binary Diameter** asks, given a set $\Sigma\subseteq\mathrm{Sym}(d)$ of permutations (as image lists) and a number $k\in\mathbb N$ written in binary, whether every element of the group $G=\langle\Sigma\rangle$ is a product of at most $k$ elements of $\Sigma$, i.e. whether $\operatorname{diam}(G,\Sigma)\le k$.
--
--   **Theorem.** The problem Binary Diameter is PSPACE-complete:
--   $$\textsc{Binary Diameter}\in\mathrm{PSPACE}\qquad\text{and}\qquad \textsc{Binary Diameter}\ \text{is PSPACE-hard, already on instances with }\Sigma=\Sigma^{-1},$$
--   where hardness refers to polynomial-time many-one reductions.
--
--   This settles the conjecture of Lohrey and Rosowski that the diameter problem with binary threshold is as hard as the length problem, and the symmetric clause covers undirected Cayley graphs such as those of mechanical puzzles.
--
--   **Formalization Note.** `InPSPACE encDiam BinaryDiameter` is membership for all instances; hardness is `PSPACEHard` over the subtype of symmetric instances with encoding `encDiam ∘ Subtype.val`. Since a reduction into the symmetric subtype is also a reduction into all instances (same output strings), the statement implies `PSPACEComplete encDiam BinaryDiameter`.
--
--   Differences from the source:
--   - generalization: PSPACE-hard → PSPACE-hard already over the symmetric instances Σ = Σ⁻¹; reason: the paper claims this on pp. 5 and 12, and it implies PSPACE-hardness over all instances, so the statement specializes to Theorem 1.1
--   - encoding: instances (Σ, k), PSPACE, polynomial-time many-one reductions → DiamInstance under encDiam (image lists, k in binary), the published InPSPACE/PSPACEHard on TM2 machines; reason: the paper's input format (pp. 3, 10); the published space measure also counts the input, harmless for polynomial bounds
--   - encoding: permutations compose left to right → Mathlib's Equiv.Perm composes right to left; reason: ℓ and diam are invariant under reversing words, so no instance changes its answer
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 4, Theorem 1.1 (proof p. 12; symmetric clause pp. 5, 12)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Problems

open Equiv OptimalQueuingComplexity.Restless

namespace PermDiameter.Binary

/-- **Theorem 1.1** (Binary Diameter). Binary Diameter is PSPACE-complete: it is in PSPACE, and it
is PSPACE-hard (polynomial-time many-one reductions) already on symmetric instances `Σ = Σ⁻¹`. -/
theorem theorem_1_1 :
    InPSPACE encDiam BinaryDiameter ∧
    PSPACEHard (fun x : {x : DiamInstance // x.Symmetric} => encDiam x.1)
      (fun x => BinaryDiameter x.1) := by sorry

end PermDiameter.Binary
