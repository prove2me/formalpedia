-- Prove2me | Theorems.Thm_QiOPoQ_Supplement_theorem_5_9
-- name    : QiOPoQ.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:14:54.823208+00:00
-- url     : https://prove2.me/theorems/97ee37dd-5c12-4a0d-bc0e-bcfc6a462467
-- title:
--   Theorem 5.9: quantum-secure qiO and one-way functions make Protocol 9 a publicly verifiable classical verification of BQP
-- statement:
--   Suppose there is an obfuscation scheme for $\mathcal C_{\mathsf{BQP}}$ satisfying qiO security against nonuniform QPT adversaries, and $g_\lambda$ is a one-way function secure against such adversaries. Then Protocol 9 is a publicly verifiable protocol for classical verification of $\mathsf{BQP}$ computations.
--
--   Precisely, let Obf be a classical PPT obfuscator for $\mathcal C_{\mathsf{BQP}}$ (Definition 3.1) with qiO security against non-uniform QPT adversaries (Definition 3.2), and $g$ a one-way function secure against non-uniform QPT inverters. For every canonical padding $X_b$ of Notation 5.1, the protocol of Figure 9 (Gen publishes $\lambda$ obfuscations, of $X_{b_i}$ where $c_i=0$ and of $X_{b_i}\circ C$ where $c_i=1$, together with $y_0=g(b)$ and $y_1=g(b\oplus c)$; the honest prover evaluates each on $|0\rangle$; Verify outputs the unique $b$ with $g(b')=y_b$) satisfies:
--
--   1. Definition 3.5: the syntax, correctness, and soundness against every non-uniform QPT prover;
--   2. Definition 3.6: Verify agrees with a deterministic classical polynomial-time PublicVerify that sees only $(1^\lambda,\mathsf{chall},\mathsf{resp})$.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any gate set with designated I, X, CNOT and an adjoint map (QiOPoQ.GateSet); reason: the statement for every such gate set specializes to the paper's fixed one; the adversary model is taken over the same gate set
--   - generalization: Notation 5.1: X_b padded canonically from b and the shape of C, padding not specified → every padding X_b (a function of b and shape(C)) with shape (|C|+1, 1, n_anc, 1), channel exactly X^b(·) and polynomial-time computable; reason: specializes to whichever canonical padding is chosen
--   - reading: X_{b} ∘ C → C followed by the designated X gate (b = 1) or I gate (b = 0) on its output wire (postX); reason: Notation 5.1: X_b is padded to the gate count of X ∘ C and I ∘ C, i.e. |C| + 1
--   - reading: C_BQP: for C of description length λ, ∥C − X^{b_C}(·)∥⋄ ≤ negl(λ) → membership of polynomial-size families (published InCBQP), one negligible function per family; reason: negl(λ) has a meaning only for a family; the base mission's reading
--   - reading: the unique bit a_λ with ∥C_λ − X^{a_λ}∥⋄ ≤ negl(λ) → every bit sequence a with ∥C_λ − X^{a_λ}(·)∥⋄ ≤ μ(λ) for a negligible μ; reason: such a sequence is unique for all large λ, and quantifying over all of them covers the unique one
--   - encoding: PPT algorithms and classical polynomial-time algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count (and advice for non-uniform ones), on fixed self-delimiting encodings; reason: the standard model; same instances as the base mission
--   - reading: non-uniform QPT algorithms (adversaries, provers, distinguishers, inverters) → NUQPT: classical advice of polynomial length, coins, a classical polynomial-time generator of circuits over the gate set run on |0…0⟩ and measured, and classical polynomial-time post-processing; reason: the paper never uses quantum advice and excludes quantum auxiliary inputs (§3.1); over a universal gate set adaptivity and intermediate measurements can be deferred into the circuits
--   - encoding: Prove evaluates each obfuscated circuit on |0⟩ and returns the measured outputs → the published fig6Prove with t = λ: the classical list of the first λ challenge components, each run on all zeros, outcomes concatenated in order; reason: the uniform-generator model of QPT used by the base mission
--   - encoding: a one-way function family {g_λ}, g_λ with input length λ → one polynomial-time map g on all strings (g_λ = g on length λ), inverted by any preimage (IsOWFQuantum); reason: the standard notion; same instances; as the published IsOWF
--   - encoding: Verify(1^λ, chall, b′); state empty → the five-argument Verify of Definition 3.5 ignoring C and the empty state; a challenge that does not parse as λ + 2 components is rejected; reason: Definition 3.6: 'A setup algorithm that returns only a public challenge fits this syntax by taking state to be the empty string'
--   - reading: Definition 3.6: every C ∈ C_BQP → every member C_m of every family in InCBQP, at every security parameter λ; reason: C_BQP is a class of families in this formalization
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 5.9, p.29; Figure 9, p.28; Notation 5.1, p.22; Definitions 3.5–3.6, pp.15–16

import Mathlib
import Definitions.Def_QiOPoQ_IsObfCorrect
import Definitions.Def_QiOPoQ_fig6Prove
import Definitions.Def_QiOPoQ_Supplement_IsQiOQuantumOn
import Definitions.Def_QiOPoQ_Supplement_IsOWFQuantum
import Definitions.Def_QiOPoQ_Supplement_IsCVQC
import Definitions.Def_QiOPoQ_Supplement_IsPubVerCVQC
import Definitions.Def_QiOPoQ_Supplement_IsCanonPadding
import Definitions.Def_QiOPoQ_Supplement_fig9Gen
import Definitions.Def_QiOPoQ_Supplement_fig9Verify

set_option autoImplicit false

open QAlgorithms.Complexity

namespace QiOPoQ.Supplement

/-- **Theorem 5.9.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and
Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 5.9,
p.29: "Suppose there is an obfuscation scheme for C_BQP satisfying qiO security against nonuniform
QPT adversaries, and g_λ is a one-way function secure against such adversaries. Then Protocol 9 is
a publicly verifiable protocol for classical verification of BQP computations."

Let `Obf` be a classical PPT obfuscator for C_BQP (Definition 3.1) with qiO security against
non-uniform QPT adversaries (Definition 3.2), and `g` a one-way function secure against
non-uniform QPT inverters. For every canonical padding `X_b` of Notation 5.1, Protocol 9 (Figure 9:
Gen `fig9Gen` with draws `fig9Rad`, the honest prover `fig6Prove λ`, which runs the `λ` challenge
circuits on `|0⟩`, and Verify `fig9Verify`, which ignores `C` and the empty state) is a protocol
for classical verification of quantum computation (Definition 3.5: syntax, correctness, soundness
against every non-uniform QPT prover) and is publicly verifiable (Definition 3.6). -/
theorem theorem_5_9 (G : GateSet) (Obf : UPPT) (hcorr : IsObfCorrect G Obf)
    (hqiO : IsQiOQuantum G Obf) (g : Str → Str) (hg : IsOWFQuantum G g)
    (Xp : Bool → ℕ × ℕ × ℕ × ℕ → Circ G) (hXp : IsCanonPadding Xp) :
    IsCVQC G (fig9Rad Obf Xp) (fig9Gen Obf Xp g) (fig6Prove fun n => n)
        (fun n _ c _ resp => fig9Verify g n c resp) ∧
      IsPubVerCVQC G (fig9Rad Obf Xp) (fig9Gen Obf Xp g)
        (fun n _ c _ resp => fig9Verify g n c resp) := by sorry

end QiOPoQ.Supplement
