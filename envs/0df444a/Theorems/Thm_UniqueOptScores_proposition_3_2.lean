-- Prove2me | Theorems.Thm_UniqueOptScores_proposition_3_2
-- name    : UniqueOptScores.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:30:12.639341+00:00
-- url     : https://prove2.me/theorems/b191f4dc-758d-44fa-8681-ec8e7ea67c59
-- title:
--   Proposition 3.2 — $\mathrm{coNP}^A \subseteq \mathrm{US}^A \subseteq \mathrm{DP}^A$ and $D^A \subseteq \Theta^{\mathrm P,A}_2$
-- statement:
--   For every oracle $A \subseteq \{0,1\}^*$,
--   $$
--   \mathrm{coNP}^A \subseteq \mathrm{US}^A \subseteq \mathrm{DP}^A \qquad\text{and}\qquad D^A \subseteq \Theta^{\mathrm P,A}_2 ,
--   $$
--   where $D^A = \mathrm P_{\mathrm{dtt}}(\mathrm{US}^A)$ is disjunctive truth-table access to a fixed $\mathrm{US}^A$ language and $\Theta^{\mathrm P,A}_2 = \mathrm P^{\mathrm{NP}^A}_\parallel$ is parallel access to a fixed $\mathrm{NP}^A$ language, both with direct access to $A$.
--
--   These are the basic containments of the relativized landscape; the last one is the top inclusion of the hierarchy of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: languages over {0,1}, oracle machines with polynomial running time valid for every oracle → Set (List Bool); HMBinPacking.OracleMachine with the set oracle [q ∈ A] and a polynomial clock quantified over all oracles A (IsClocked); reason: Lean convention for the paper's model (p.15, p.16); same instances
--   - encoding: nondeterministic polynomial-time oracle machines and their accepting computations (NP^A, US^A) → clocked deterministic verifiers over witnesses of length exactly p(|x|) (HMBinPacking.OracleMachine, pairing ⟨x, y⟩, acceptance = output 1); reason: paths are zero-padded choice strings of a common length (p.13), so accepting computations are in bijection with accepted witnesses; same classes
--   - encoding: transducer output list (y1, …, ym) → bit-doubled entries with separator 01, malformed output decoded as the empty list; reason: the paper's convention "Malformed lists become empty lists" (p.27); same class
--   - encoding: Θ^{P,A}_2 = P^{NP^A}_∥: polynomial-time computation with direct access to A and polynomially many nonadaptive queries to a fixed NP^A language → a clocked query generator T and a clocked decision machine E, both with oracle A, E accepting ⟨x, answer vector⟩ for the list output by T; reason: truth-table form of nonadaptive access (all NP^A queries prepared before any answer, p.14); E may recompute T; same class
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Proposition 3.2, p.15

import Mathlib
import Definitions.Def_UniqueOptScores_coNP
import Definitions.Def_UniqueOptScores_US
import Definitions.Def_UniqueOptScores_DP
import Definitions.Def_UniqueOptScores_Dtt
import Definitions.Def_UniqueOptScores_Theta2

namespace UniqueOptScores

/-- **Proposition 3.2 (basic containments).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Proposition 3.2, p.15: "For every oracle A, coNP^A ⊆ US^A ⊆ DP^A and D^A ⊆ Θ^{P,A}_2." -/
theorem proposition_3_2 (A : Set (List Bool)) :
    coNP A ⊆ US A ∧ US A ⊆ DP A ∧ Dtt A ⊆ Theta2 A := by sorry

end UniqueOptScores
