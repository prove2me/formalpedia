-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_D_30
-- name    : QuantumKtSoI.Supplement.theorem_D_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:51:06.804909+00:00
-- url     : https://prove2.me/theorems/54adeeda-3434-47f7-8993-c4125216bc2a
-- title:
--   Theorem D.30, p.181 — a quasi-linear interpreter $I$ of descriptions
-- statement:
--   There are a machine $I$ of Definition 3.1 and a polynomial $p_I$ with nonnegative coefficients such that, for every description $e$, all strings $x,y$ and every integer $t\ge1$,
--   $$P_I\big(\langle e,x\rangle;\ p_I(|e|+\log(t+|x|+2))\,(t+|x|+|e|+1),\ y\big)\ge P_e(x;t,y).$$
--
--   The interpreter simulates every description with an overhead that is linear in the running time up to a factor polynomial in the description length and the logarithm of the time.
--
--   **Formalization Note** $p_I$ is a real polynomial evaluated at a real argument and the deadline is a floor.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a machine of Definition 3.1 → a valid coded machine of the base mission (CodedMachine with Valid), halting on every branch by the floor of the stated deadline; reason: the base mission's representation of machines; halting within a time bound is all-branch and real deadlines are floors (p.22)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem D.30, p.181

import Mathlib
import Definitions.Def_QuantumKtSoI_Supplement_qKtU

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem D.30** (Quasi-linear interpreter; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.181). There are a machine `I` of
Definition 3.1 and a polynomial `p_I` with nonnegative coefficients such that, for every description
`e`, all strings `x, y` and every integer `t ≥ 1`,
`P_I(⟨e, x⟩; p_I(|e| + log(t + |x| + 2))(t + |x| + |e| + 1), y) ≥ P_e(x; t, y)`.

**Formalization Note** `InterpreterProp`: `I` is a valid coded machine, `p_I` a real polynomial
with nonnegative coefficients, the deadline is read as `⌊·⌋` (p.22), and `⟨e, x⟩` pairs the bit
string of `e`. Descriptions and `P_e` are those of the admissible glue routine set `G` (p.24). -/
theorem theorem_D_30 (G : GlueRoutines) (hG : G.Admissible) :
    ∃ I : CodedMachine, ∃ pI : Polynomial ℝ, InterpreterProp G I pI := by sorry

end QuantumKtSoI.Supplement
