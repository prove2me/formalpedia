-- Prove2me | Theorems.Thm_TetraOT_thm_4_1_correctness
-- name    : TetraOT.thm_4_1_correctness
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:21.194624+00:00
-- url     : https://prove2.me/theorems/9a1f7817-f93f-4886-8e77-6b83d141bf35
-- title:
--   Correctness of the Tetrahedral Protocol — $y_s = m_s$ on all 24 deals
-- statement:
--   Run the Tetrahedral Protocol on a deal $\rho \in S_4$: Alice computes $(M, m_0, m_1) = A(\rho(0),\rho(1))$ and Bob computes $(y_0,y_1) = B(M,\rho(2))$, recorded as his selection bit $s$ and his bit $y_s$. There are $|S_4| = 24$ deals, hence 24 equally likely transcripts, and on every one of them Bob's bit is Alice's bit in the selected position:
--   $$
--   y_s = m_s \qquad \text{for all } \rho \in S_4 .
--   $$
--
--   This is the correctness half of Theorem 4.1: the protocol always delivers a valid oblivious-transfer output pair.
--
--   **Formalization Note** Bob's output is the pair $(s, m_s)$ of Booleans ($\texttt{true}=1$), and $m_s$ is $m_1$ if $s = 1$ and $m_0$ if $s = 0$.
--
--   Differences from the source:
--   - encoding: Bob records $(y_0, y_1)$ with $y_s = m_s$, $y_{1-s} = \bullet$ → Bob's output is the pair $(s, m_s)$ of Booleans; reason: a one-to-one recoding of the four patterns $0\bullet, 1\bullet, \bullet0, \bullet1$ (right dot = $s=0$, Fig. 5 caption)
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Theorem 4.1, proof, first paragraph, p.3 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg
import Definitions.Def_TetraOT_aliceTable
import Definitions.Def_TetraOT_bobTable
import Definitions.Def_TetraOT_tetrahedralRun

set_option autoImplicit false

namespace TetraOT

/-- **Correctness of the Tetrahedral Protocol** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Theorem 4.1, proof, first paragraph, p.3;
p. = PDF page, the PDF has no printed page numbers): "Since Alice and Bob are deterministic, there are
24 equally likely protocol transcripts, one for each permutation of the deck. The tables are
constructed to ensure that yₛ = mₛ for all 24 permutations, making correctness of the outputs trivial
to check." There are 24 deals, and on every deal Bob's recorded bit is the selected bit of Alice's
output.

**Formalization Note.** Bob's output `(s, m_s)` encodes his `(y₀, y₁)`, so "`y_s = m_s`" reads
`(bobOut ρ).2 = if (bobOut ρ).1 then (aliceOut ρ).2 else (aliceOut ρ).1` (with `true` = 1). -/
theorem thm_4_1_correctness :
    Fintype.card (Equiv.Perm (Fin 4)) = 24 ∧
    ∀ ρ : Equiv.Perm (Fin 4),
      (bobOut ρ).2 = (if (bobOut ρ).1 then (aliceOut ρ).2 else (aliceOut ρ).1) := by sorry

end TetraOT
