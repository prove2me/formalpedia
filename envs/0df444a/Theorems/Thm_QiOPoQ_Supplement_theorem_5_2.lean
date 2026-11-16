-- Prove2me | Theorems.Thm_QiOPoQ_Supplement_theorem_5_2
-- name    : QiOPoQ.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:12:37.605346+00:00
-- url     : https://prove2.me/theorems/1ceb1dac-ce63-4f84-a546-e5c108875055
-- title:
--   Theorem 5.2: quantum-secure qiO makes Protocol 7 a privately verifiable, blind classical verification of BQP
-- statement:
--   Suppose there is an obfuscation scheme for $\mathcal C_{\mathsf{BQP}}$ satisfying qiO security against QPT adversaries. Then Protocol 7 is a privately verifiable and blind protocol for classical verification of $\mathsf{BQP}$.
--
--   Precisely, let Obf be a classical PPT obfuscator for $\mathcal C_{\mathsf{BQP}}$ (Definition 3.1) with qiO security against non-uniform QPT adversaries (Definition 3.2). For every choice of $\mathrm{rows},\mathrm{cols}$ as in Notation 5.1 ($\lambda\le\mathrm{rows}\le\mathrm{poly}(\lambda)$, $2\le\mathrm{cols}\le\mathrm{poly}(\lambda)$, computable from $1^\lambda$) and every canonical padding $X_b$ of Notation 5.1, the protocol of Figure 7 (Gen plants $X_{b_{i,j}}\circ C$ at one uniformly random position per row of a $\mathrm{rows}\times\mathrm{cols}$ grid of obfuscations of $X_{b_{i,j}}$; the honest prover evaluates every obfuscated circuit on $|0\rangle$; Verify checks the test positions and decodes the planted ones) satisfies:
--
--   1. Definition 3.5: the syntax, correctness, and soundness against every non-uniform QPT prover;
--   2. blindness: one classical PPT simulator given only $(1^\lambda,\mathrm{shape}(C_\lambda))$ produces challenges that no non-uniform QPT distinguisher tells apart from real ones, for every polynomial-size family in $\mathcal C_{\mathsf{BQP}}$.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any gate set with designated I, X, CNOT and an adjoint map (QiOPoQ.GateSet); reason: the statement for every such gate set specializes to the paper's fixed one; the adversary model is taken over the same gate set
--   - generalization: Notation 5.1: rows, cols with λ ≤ rows ≤ poly(λ), 2 ≤ cols ≤ poly(λ), efficiently computable → every pair satisfying IsRowsCols; reason: the paper leaves the choice open; specializes to any choice
--   - generalization: Notation 5.1: X_b padded canonically from b and the shape of C, padding not specified → every padding X_b (a function of b and shape(C)) with shape (|C|+1, 1, n_anc, 1), channel exactly X^b(·) and polynomial-time computable; reason: specializes to whichever canonical padding is chosen
--   - reading: X_{b} ∘ C → C followed by the designated X gate (b = 1) or I gate (b = 0) on its output wire (postX); reason: Notation 5.1: X_b is padded to the gate count of X ∘ C and I ∘ C, i.e. |C| + 1
--   - reading: C_BQP: for C of description length λ, ∥C − X^{b_C}(·)∥⋄ ≤ negl(λ) → membership of polynomial-size families (published InCBQP), one negligible function per family; reason: negl(λ) has a meaning only for a family; the base mission's reading
--   - reading: the unique bit a_λ with ∥C_λ − X^{a_λ}∥⋄ ≤ negl(λ) → every bit sequence a with ∥C_λ − X^{a_λ}(·)∥⋄ ≤ μ(λ) for a negligible μ; reason: such a sequence is unique for all large λ, and quantifying over all of them covers the unique one
--   - encoding: PPT algorithms and classical polynomial-time algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count (and advice for non-uniform ones), on fixed self-delimiting encodings; reason: the standard model; same instances as the base mission
--   - reading: non-uniform QPT algorithms (adversaries, provers, distinguishers, inverters) → NUQPT: classical advice of polynomial length, coins, a classical polynomial-time generator of circuits over the gate set run on |0…0⟩ and measured, and classical polynomial-time post-processing; reason: the paper never uses quantum advice and excludes quantum auxiliary inputs (§3.1); over a universal gate set adaptivity and intermediate measurements can be deferred into the circuits
--   - encoding: Gen is a classical PPT algorithm sampling uniform bits and uniform elements of [cols] → Gen is a polynomial-time map applied to independent uniform draws whose ranges (2 or cols) are computed in polynomial time; reason: samples j*_i exactly uniformly from [cols], as Figure 7 prints, also when cols is not a power of two
--   - encoding: Prove evaluates each obfuscated circuit on |0⟩ and returns the measured outputs → the published fig6Prove with t = rows·cols: the classical list of the first rows·cols challenge components, each run on all zeros, outcomes concatenated in order; reason: the uniform-generator model of QPT used by the base mission
--   - encoding: chall = (Ĉ_{i,j})_{i,j}, state = (J*, b) → tuple code of the entries in row-major order; state = (tuple of the j*_i in unary, the mask bits); reason: a fixed injective layout
--   - encoding: Verify outputs a bit or ⊥ → Option Bool, none = ⊥; an unparsable state or response, and the case rows = 0 (no planted value), give ⊥; reason: the printed test; rows = 0 occurs only at λ = 0
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 5.2, p.24; Figure 7, p.23; Notation 5.1, p.22; Definition 3.5, pp.15–16

import Mathlib
import Definitions.Def_QiOPoQ_IsObfCorrect
import Definitions.Def_QiOPoQ_fig6Prove
import Definitions.Def_QiOPoQ_Supplement_IsQiOQuantumOn
import Definitions.Def_QiOPoQ_Supplement_IsCVQC
import Definitions.Def_QiOPoQ_Supplement_IsBlindCVQC
import Definitions.Def_QiOPoQ_Supplement_IsRowsCols
import Definitions.Def_QiOPoQ_Supplement_IsCanonPadding
import Definitions.Def_QiOPoQ_Supplement_fig7Gen
import Definitions.Def_QiOPoQ_Supplement_fig7Verify

set_option autoImplicit false

open QAlgorithms.Complexity

namespace QiOPoQ.Supplement

/-- **Theorem 5.2.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and
Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 5.2,
p.24: "Suppose there is an obfuscation scheme for C_BQP satisfying qiO security against QPT
adversaries. Then, Protocol 7 is a privately verifiable and blind protocol for classical
verification of BQP."

Let `Obf` be a classical PPT obfuscator for C_BQP (Definition 3.1) with qiO security against
non-uniform QPT adversaries (Definition 3.2). For every choice of `rows, cols` as in Notation 5.1
(computable from `1^λ`, `λ ≤ rows ≤ poly(λ)`, `2 ≤ cols ≤ poly(λ)`) and every canonical padding
`X_b` of Notation 5.1, Protocol 7 (Figure 7: Gen `fig7Gen` with draws `fig7Rad`, the honest
prover `fig6Prove (rows·cols)`, which runs the `rows·cols` challenge circuits on `|0⟩`, and Verify
`fig7Verify`) is a protocol for classical verification of quantum computation (Definition 3.5:
syntax, correctness, soundness against every non-uniform QPT prover) and is blind (Definition 3.5:
a PPT simulator from `(1^λ, shape(C_λ))` fools every non-uniform QPT distinguisher). -/
theorem theorem_5_2 (G : GateSet) (Obf : UPPT) (hcorr : IsObfCorrect G Obf)
    (hqiO : IsQiOQuantum G Obf) (rows cols : ℕ → ℕ) (hrc : IsRowsCols rows cols)
    (Xp : Bool → ℕ × ℕ × ℕ × ℕ → Circ G) (hXp : IsCanonPadding Xp) :
    IsCVQC G (fig7Rad Obf Xp rows cols) (fig7Gen Obf Xp rows cols)
        (fig6Prove fun n => rows n * cols n) (fig7Verify rows cols) ∧
      IsBlindCVQC G (fig7Rad Obf Xp rows cols) (fig7Gen Obf Xp rows cols) := by sorry

end QiOPoQ.Supplement
