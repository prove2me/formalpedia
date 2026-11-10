-- Prove2me | Theorems.Thm_TetraOT_thm_4_1_alice_uniform
-- name    : TetraOT.thm_4_1_alice_uniform
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:31.024059+00:00
-- url     : https://prove2.me/theorems/4b95204a-d3a4-4558-93e5-93e6795b07a5
-- title:
--   In the Tetrahedral Protocol each $m_0m_1$ arises from exactly 6 deals, so Alice's output is uniform
-- statement:
--   In the Tetrahedral Protocol on a deal $\rho\in S_4$, Alice's output is $(m_0, m_1)$, read from her table at her ordered hand $(\rho(0),\rho(1))$. For each of the four values of $(m_0, m_1) \in \{0,1\}^2$, exactly 6 of the 24 deals produce it:
--   $$
--   \#\{\rho \in S_4 : (m_0, m_1)(\rho) = (a, b)\} = 6 \qquad \text{for all } (a,b)\in\{0,1\}^2,
--   $$
--   and consequently, when $\rho$ is uniform on $S_4$, Alice's output is uniform on $\{0,1\}^2$.
--
--   This is the first step of the privacy argument against a semi-honest Alice in Theorem 4.1: her outputs have exactly the ideal marginal law.
--
--   **Formalization Note** A transcript is identified with its deal $\rho$, since both parties act deterministically. The deal is the uniform `PMF` on `Equiv.Perm (Fin 4)` and Alice's output law is its image.
--
--   Differences from the source:
--   - encoding: "transcripts producing $m_0m_1$" → permutations $\rho$ with Alice's output $(m_0,m_1)$; reason: the run is deterministic, with one transcript per permutation (proof of Theorem 4.1, first paragraph)
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Theorem 4.1, proof, paragraph "First, consider Alice's view", p.3 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg
import Definitions.Def_TetraOT_aliceTable
import Definitions.Def_TetraOT_bobTable
import Definitions.Def_TetraOT_tetrahedralRun

set_option autoImplicit false

namespace TetraOT

/-- **Alice's outputs are uniform** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Theorem 4.1, proof, paragraph "First, consider Alice's
view", p.3; p. = PDF page, the PDF has no printed page numbers): "For any pair m₀m₁, there are
precisely 6 transcripts producing it. Thus her outputs are uniformly random." Each of the four values of
`(m₀, m₁)` is produced by exactly 6 of the 24 permutations, and under the uniform deal Alice's output
is uniform on `Bool × Bool`.

**Formalization Note.** A transcript is a permutation `ρ` (the run is deterministic), so "transcripts
producing m₀m₁" is the set of `ρ` with `aliceOut ρ = (m₀, m₁)`. -/
theorem thm_4_1_alice_uniform :
    (∀ m : Bool × Bool,
      (Finset.univ.filter (fun ρ : Equiv.Perm (Fin 4) => aliceOut ρ = m)).card = 6) ∧
    deal.map aliceOut = PMF.uniformOfFintype (Bool × Bool) := by sorry

end TetraOT
