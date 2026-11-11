-- Prove2me | Theorems.Thm_PermDiameter_Binary_theorem_4_1
-- name    : PermDiameter.Binary.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:11:19.774203+00:00
-- url     : https://prove2.me/theorems/0a5f0b7e-6d8a-4c65-b747-50a7ab492f5e
-- title:
--   Theorem 4.1 — Binary Length is PSPACE-complete, even for 3-step nilpotent metabelian groups
-- statement:
--   The problem Binary Length (given $\Sigma\subseteq\mathrm{Sym}(d)$, $g\in\langle\Sigma\rangle$ and $k$ in binary, decide $\ell(g,\Sigma)\le k$) is PSPACE-complete, even when restricted to groups $G=\langle\Sigma\rangle$ that are simultaneously 3-step nilpotent ($\gamma_3(G)=1$) and metabelian ($G^{(2)}=1$). Precisely:
--
--   1. Binary Length is in PSPACE (for arbitrary permutation groups);
--   2. the restricted language $\{(\Sigma,g,k): \langle\Sigma\rangle \text{ 3-step nilpotent and metabelian},\ \ell(g,\Sigma)\le k\}$ is in PSPACE;
--   3. Binary Length is PSPACE-hard under polynomial-time many-one reductions already on the instances with $g\in\langle\Sigma\rangle$ and $\langle\Sigma\rangle$ 3-step nilpotent and metabelian.
--
--   $$\textsc{Binary Length}\in\mathrm{PSPACE},\qquad \textsc{Binary Length}\big|_{\gamma_3=1,\ G^{(2)}=1}\ \text{is PSPACE-hard}.$$
--   It strengthens Jerrum's theorem and supplies both the hardness and the polynomial-space procedure that the proof of Theorem 1.1 uses.
--
--   **Formalization Note.** PSPACE and hardness are the published `InPSPACE` and `PSPACEHard` (TM2 machines, space = total stack length, reductions `TM2ComputableInPolyTime`). The restricted hardness is `PSPACEHard` over the subtype of valid, 3-step nilpotent, metabelian instances with encoding `encLength ∘ Subtype.val`, so every reduction output satisfies the restriction.
--
--   Differences from the source:
--   - encoding: "PSPACE-complete, even when restricted to (3-step nilpotent, metabelian) groups" → InPSPACE of the general language ∧ InPSPACE of the restricted language ∧ PSPACEHard over the subtype of restricted instances; reason: together these cover both the language and the promise readings of the restriction
--   - encoding: instances (Σ, g, k) with g ∈ G; PSPACE, many-one reductions → encLength (image lists, k binary), BinaryLength false when g ∉ ⟨Σ⟩, the published InPSPACE/PSPACEHard; reason: the published space measure also counts the input, harmless for polynomial bounds
--   - encoding: permutations compose left to right → Mathlib's Equiv.Perm composes right to left; reason: ℓ is invariant under reversing words, and γ₃ = 1 and G⁽²⁾ = 1 hold for a group iff they hold for its opposite
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 21, Theorem 4.1 (proof §4.4, pp. 26–27)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Problems

open Equiv OptimalQueuingComplexity.Restless

namespace PermDiameter.Binary

/-- **Theorem 4.1.** Binary Length is PSPACE-complete, even when restricted to groups that are
simultaneously 3-step nilpotent and metabelian: the general problem is in PSPACE, the restricted
language is in PSPACE, and the problem is PSPACE-hard already on the instances with `g ∈ ⟨Σ⟩`
and `⟨Σ⟩` 3-step nilpotent and metabelian. -/
theorem theorem_4_1 :
    InPSPACE encLength BinaryLength ∧
    InPSPACE encLength (fun x => x.NilpotentMetabelian ∧ BinaryLength x) ∧
    PSPACEHard (fun x : {x : LengthInstance // x.Valid ∧ x.NilpotentMetabelian} => encLength x.1)
      (fun x => BinaryLength x.1) := by sorry

end PermDiameter.Binary
