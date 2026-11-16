-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_Supplement_theorem_B_3
-- name    : QAdvFew.PoQOracle.Supplement.theorem_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:26:54.156736+00:00
-- url     : https://prove2.me/theorems/b10f91c3-6802-45f4-b7a7-59f234757706
-- title:
--   Theorem B.3 — EV-OWPuzzs from commitments with a classical committer
-- statement:
--   If commitments as in Definition B.1 exist (statistically sum-binding, computationally hiding, with a classical PPT committer and a quantum receiver, in the plain model), then efficiently verifiable one-way puzzles exist with
--
--   1. perfect correctness,
--   2. a QPT sampler, and
--   3. a classical deterministic polynomial-time verifier.
--
--   Combined with Theorem B.2 (OSP implies such commitments, [BK25]), this shows that classically verifiable OSP implies EV-OWPuzzs, and hence $\mathsf{BQP}\neq\mathsf{QCMA}$.
--
--   Differences from the source:
--   - reading: EV-OWPuzzs ([CGG24]; not restated in the paper) → a uniform QPT sampler Samp(1^n) → (s, k), a polynomial-time verification function, Pr[Ver(s, k) = 1] = 1 for every n, and Pr[Ver(s, A(s)) = 1] negligible for every nonuniform QPT A; reason: the standard [CGG24] notion with the properties Theorem B.3 asks for
--   - encoding: a computationally unbounded committer with private state σ → conditional laws (PMF) of each committer message given the earlier messages and of the opening (or no opening) given the transcript and b'; reason: with classical communication this is exactly what such a committer induces
--   - encoding: PPT Com and Open; QPT Rec and Ver → polynomial-time functions of the input and polynomially many coins; uniform polynomially bounded circuit families; the opening d of fixed polynomial length; reason: Lean representation; a polynomial-time Ver reads polynomially many bits of d
--   - encoding: nonuniform QPT receivers (hiding) and adversaries (puzzle security) → polynomial-size circuit families without quantum advice in both places; reason: §3.2.1: "We do not allow quantum advice unless stated explicitly"; one notion throughout
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem B.3, p. 53 (PDF p. 55)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_Commitment
import Definitions.Def_QAdvFew_PoQOracle_Supplement_EVOWPuzz

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

/-- **Theorem B.3** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem B.3, p. 53 (PDF p. 55)): "If commitments as in Definition B.1 exist,
then EV-OWPuzzs exist with perfect correctness, a QPT sampler, and a classical deterministic
polynomial-time verifier."

In the plain model: if some `Commitment` satisfies Definition B.1 (`IsCommitment`), then some
`EVOWPuzz` (QPT sampler, deterministic polynomial-time verifier) is perfectly correct and secure
against every nonuniform QPT adversary (`IsPerfect`).

**Formalization Note** Nonuniform QPT receivers (hiding) and adversaries (puzzle security) are both
polynomial-size circuit families without quantum advice. -/
theorem theorem_B_3 (h : ∃ Cm : Commitment, Cm.IsCommitment) : ∃ P : EVOWPuzz, P.IsPerfect := by sorry

end QAdvFew.PoQOracle.Supplement
