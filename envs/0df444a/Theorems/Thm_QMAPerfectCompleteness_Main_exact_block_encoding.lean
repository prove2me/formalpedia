-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_exact_block_encoding
-- name    : QMAPerfectCompleteness.Main.exact_block_encoding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:47.785571+00:00
-- url     : https://prove2.me/theorems/fc142b6c-e060-40a3-8fcc-ebcaba8430c8
-- title:
--   Lemma 3.6 — exact, efficient block encoding of $I-C_{z,a/b}$
-- statement:
--   For every valid certificate $(z,a,b)$ the unitary $U_{z,a,b}$ of Eq. (7) satisfies
--
--   $$
--   (\langle0|_Z\otimes I)\,U_{z,a,b}\,(|\eta\rangle_Z\otimes I)=\frac aM\,(I-C_{z,a/b}).
--   $$
--
--   Moreover $U_{z,a,b}$ has a polynomial-size circuit over $\mathcal G_2$, computable in polynomial time from $V$ and the certificate, that applies $V$ and $V^\dagger$ once each and uses additional workspace qubits that start and end in $|0\rangle$.
--
--   In precise terms, one polynomial-time machine and one polynomial $p$ serve all verifiers and certificates. The machine outputs a gate list $\mathrm{pre}\cdot V\cdot\mathrm{mid}\cdot V^\dagger\cdot\mathrm{post}$ on the block register and $w$ workspace wires, whose unitary implements $U_{z,a,b}$ with clean workspace. The number of gates in $\mathrm{pre},\mathrm{mid},\mathrm{post}$ together, plus $w$, is at most $p(k+c+m)$, where $c$ is the number of clock qubits. This bound is in terms of $k=\log_2M$, not the exponentially large $M$. With this lemma the exact kernel test becomes an operation over the gate set.
--
--   A second polynomial-time machine generates the surrounding lists and workspace count from the register layout, output-wire address, index size and certificate alone. It receives no gate list of $V$. Thus the circuit has precisely the two displayed verifier calls, and the same surrounding circuit works for verifiers with the same layout and index size.
--
--   Differences from the source:
--   - generalization: the fixed verifier $V$ of Lemma 3.1 on one input, with $g\ge1$ → any verifier $V$ over $\mathcal G_2$, with no lower bound on $g$; reason: the statement specializes to the source's verifier; the construction does not use $g\ge1$
--   - encoding: the circuit applies $V$ and $V^\dagger$ once each → a gate list pre ++ V ++ mid ++ reverse(V) ++ post, with surrounding lists generated from layout and certificate data alone, independently of the gate list of V; reason: the construction on p. 10 uses V and its inverse unconditionally; every other operation depends only on register sizes, the output-wire address and the certificate
--   - encoding: a polynomial-size circuit with workspace returned to zero → a fixed wire order with bit $i$ on the $i$-th wire of a register, and the relation `Implements` on basis states; reason: the source fixes no layout, and any layout can be permuted to this one
--   - encoding: polynomial-time generation from the verifier and certificate → uniform TM2 polynomial-time machines on self-delimiting unary circuit/layout codes and fixed-width binary certificate values; reason: these encodings have polynomial length in the local circuit description and k, and can be parsed in polynomial time
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), p. 10, Lemma 3.6 and its proof

import Definitions.Def_QMAPerfectCompleteness_Main_Compiler

open Matrix

namespace QMAPerfectCompleteness.Main

/-- Lemma 3.6 (p. 10). For every valid certificate, `(⟨0|_Z ⊗ I) U_{z,a,b} (|η⟩ ⊗ I) =
(a/M)(I - C_{z,a/b})`. Further, one polynomial-time machine computes from `V` and the certificate a
circuit over `𝒢₂` for `U_{z,a,b}`, of the form `pre ++ V ++ mid ++ V† ++ post`, where the size of
`pre`, `mid`, `post` and the number of workspace wires, which start and end in `|0⟩`, are at most
one polynomial in `k`, the number of clock qubits and `m`. A second polynomial-time machine
computes `pre`, `mid`, `post` and the workspace count from layout and certificate data alone,
without access to the gate list of `V`. Thus the only verifier calls are the displayed `V` and `V†`. -/
theorem exact_block_encoding :
    (∀ (V : Verifier gatesG2) (z : V.Proof) (a b : ℕ), IsValidCertificate V a b →
      (V.zEmbed (indexQubits V) false)ᴴ * V.blockUnitary (indexQubits V) z a b *
          V.zEmbed (indexQubits V) true =
        ((a : ℂ) / (2 : ℂ) ^ indexQubits V) • (1 - V.cyclicOp z ((a : ℝ) / b))) ∧
    ∃ (compile scaffold : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str)
        (p : Polynomial ℕ),
      QAlgorithms.Complexity.PolyTimeComputable compile ∧
      QAlgorithms.Complexity.PolyTimeComputable scaffold ∧
      ∀ (V : Verifier gatesG2) (z : V.Proof) (a b : ℕ), IsValidCertificate V a b →
        ∃ (w : ℕ) (pre mid post : List (Instr gatesG2 (BlockCircuit.bodyWires V + w))),
          compile (BlockCircuit.encodeInput V z a b) =
            BlockCircuit.encodeCircuit
              (pre ++ BlockCircuit.forwardGates V w ++ mid ++ BlockCircuit.backwardGates V w ++ post) ∧
          scaffold (BlockCircuit.encodeLayout V z a b) =
            BlockCircuit.encodeScaffold V w pre mid post ∧
          pre.length + mid.length + post.length + w ≤
            p.eval (indexQubits V + BlockCircuit.clockWires V + V.proofQubits) ∧
          BlockCircuit.Implements
            (circuitMatrix
              (pre ++ BlockCircuit.forwardGates V w ++ mid ++ BlockCircuit.backwardGates V w ++ post))
            (V.blockUnitary (indexQubits V) z a b) := by sorry

end QMAPerfectCompleteness.Main
