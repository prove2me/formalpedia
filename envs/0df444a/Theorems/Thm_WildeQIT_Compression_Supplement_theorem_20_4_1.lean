-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_20_4_1
-- name    : WildeQIT.Compression.Supplement.theorem_20_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:16:42.237528+00:00
-- url     : https://prove2.me/theorems/d45242e6-e5ea-4e64-b433-67626b019b4f
-- title:
--   Theorem 20.4.1: $\chi(\mathcal N_H\otimes\mathcal N)=\chi(\mathcal N_H)+\chi(\mathcal N)$ for a Hadamard channel $\mathcal N_H$
-- statement:
--   Let $\mathcal N_H$ be a quantum Hadamard channel (its complementary channel is entanglement-breaking) and let $\mathcal N$ be any quantum channel. Then the Holevo information is additive:
--
--   $$
--   \chi(\mathcal N_H\otimes\mathcal N)=\chi(\mathcal N_H)+\chi(\mathcal N),
--   $$
--
--   where $\chi(\mathcal N)=\max_{\rho_{XA}}I(X;B)$ over classical–quantum inputs (Definition 13.3.1).
--
--   Taking $\mathcal N=\mathcal N_H^{\otimes(n-1)}$ and iterating shows that the classical capacity of a Hadamard channel is its Holevo information.
--
--   **Formalization Note** $\chi$ is the published `WildeQIT.Degradable.holevoInfoChannel`, $\otimes$ the published `WildeQIT.Degradable.tensorChannel`; the second channel has arbitrary input and output dimensions.
--
--   Differences from the source:
--   - encoding: Hilbert spaces of positive dimension (implicit) → `[Nonempty a]` and `[Nonempty c]` on both input spaces; reason: on a zero-dimensional input there is no state and χ is the empty supremum 0, for which additivity fails; the hypotheses exclude only that case
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 20.4.1, p. 573, eq. (20.71); §5.2.3, p. 196

import Mathlib
import Definitions.Def_WildeQIT_Compression_Supplement_IsHadamard
import Definitions.Def_WildeQIT_Degradable_holevoInfoChannel
import Definitions.Def_WildeQIT_Degradable_tensorChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 20.4.1, p. 573.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 20.4.1** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 573, (20.71)): "The Holevo information of a quantum Hadamard
channel `N_H` and any other channel `N` is additive: `χ(N_H ⊗ N) = χ(N_H) + χ(N)`."

Formalization Note: `χ` is the published `WildeQIT.Degradable.holevoInfoChannel` (Definition
13.3.1, maximum over mixed classical–quantum inputs), `⊗` the published
`WildeQIT.Degradable.tensorChannel`, a Hadamard channel `IsHadamard` (complement
entanglement-breaking, §5.2.3). The second channel is arbitrary, with any input and output
dimensions. The input spaces are nonempty (Hilbert spaces of positive dimension): on a
zero-dimensional input there is no state and `χ` would be the empty supremum `0`. -/
theorem theorem_20_4_1 {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] [Nonempty a] [Nonempty c]
    (NH : QChannel a b) (hNH : IsHadamard NH) (N : QChannel c d) :
    WildeQIT.Degradable.holevoInfoChannel (WildeQIT.Degradable.tensorChannel NH N) =
      WildeQIT.Degradable.holevoInfoChannel NH + WildeQIT.Degradable.holevoInfoChannel N := by sorry

end WildeQIT.Compression.Supplement
