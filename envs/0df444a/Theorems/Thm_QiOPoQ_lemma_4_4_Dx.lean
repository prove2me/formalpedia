-- Prove2me | Theorems.Thm_QiOPoQ_lemma_4_4_Dx
-- name    : QiOPoQ.lemma_4_4_Dx
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:43.690287+00:00
-- url     : https://prove2.me/theorems/f89baaef-0bfa-454d-94ac-8459360b5ec6
-- title:
--   Lemma 4.4, proof, eq. (3): $D_x$ has the padded shape and implements $X^{L(x)}(\cdot)$
-- statement:
--   Let $L$ be decided by the uniformly generated circuits $V_\lambda$ and let $C_{b,\lambda}$ be a padding. Then:
--
--   1. $\mathrm{shape}(D_x)=\mathrm{shape}(C_{b,\lambda})$ for every $\lambda$, $x$ and $b$;
--   2. there is a negligible $\mu$ with, for every $\lambda$ and every $x\in\{0,1\}^\lambda$,
--
--   $$
--   \|D_x(\cdot)-X^{L(x)}(\cdot)\|_\diamond\le\mu(\lambda);
--   $$
--
--   3. for every choice of one string $x_\lambda\in\{0,1\}^\lambda$ per length, the family $\{D_{x_\lambda}\}$ is in $\mathcal C_{\mathsf{BQP}}$;
--   4. there is a negligible $\mu$ with $\|D_x-C_{L(x),\lambda}\|_\diamond\le\mu(\lambda)$ for all $\lambda$ and $x\in\{0,1\}^\lambda$.
--
--   This is what lets qiO security be applied to the pair $D_x$ and $C_{L(x),\lambda}$.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any finite gate set with designated I, X, CNOT and an adjoint map; reason: no step uses universality; every universal gate set of the required form is an instance
--   - reading: BQP ⊄ i.o.P/poly, with Notation 4.1 choosing L ∈ BQP \ i.o.P/poly and V_λ → for every L ∉ i.o.P/poly decided by uniformly generated V_λ with negligible error and an ancilla output wire; reason: the construction is built from this datum (Notation 4.1, proof of Lemma 4.4); the universal quantifier covers whichever choice is made
--   - generalization: C_{b,λ}: "Pad C_{b,λ} so that it has the required gate count", no specific padding → every family with the printed shape, output wire, channel X^b(·) and polynomial-time construction; reason: specializes to whichever padding is chosen
--   - reading: C_BQP: for C of description length λ, ∥C − X^{b_C}(·)∥⋄ ≤ negl(λ) → membership of polynomial-size families, with one negligible function per family; reason: negl(λ) has a meaning only for a family; Definition 3.2 quantifies over polynomial-size families
--   - encoding: ∥·∥⋄, normalization not fixed by the paper → supremum over pure states with a same-size reference, no factor ½; reason: a constant factor does not affect ≤ negl(λ)
--   - reading: "every D_x belongs to C_BQP" → for every choice x_λ the family λ ↦ D_{x_λ} is in the family-level class, and the bound (3) is uniform in x; reason: needed for a family-level class; the proof selects a worst x_λ
--   - generalization: the proof of Lemma 4.4, under its hypotheses (qiO scheme, L ∉ i.o.P/poly) → only the decider V_λ and the padding; no obfuscator and no hypothesis L ∉ i.o.P/poly; reason: eq. (3) uses only the negligible error of V_λ and the shape of C_{b,λ}; it specializes to the proof context
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), proof of Lemma 4.4, pp.18–19, eq. (3)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_InCBQP
import Definitions.Def_QiOPoQ_IsDecider
import Definitions.Def_QiOPoQ_IsPadding
import Definitions.Def_QiOPoQ_IsAdmissibleRounds
import Definitions.Def_QiOPoQ_Dx
set_option autoImplicit false
open QAdvFew.PoQOracle QAlgorithms.Complexity

namespace QiOPoQ

open Classical in
/-- **Proof of Lemma 4.4: the circuits `D_x` have the shape of `C_{b,λ}` and implement
`X^{L(x)}`.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), proof of Lemma 4.4, pp.18–19: "Each D_x has 2|V_λ| + 2λ + 1 gates and uses
the output, instance, and workspace registers of V_λ as its clean workspace, so it has the same
shape as C_{0,λ} and C_{1,λ} in Notation 4.1. By the negligible error guarantee of V_λ, we know
that ∥D_x(·) − X^{L(x)}(·)∥⋄ ≤ negl(λ), (3) and therefore every D_x belongs to C_BQP and is
negligibly close to C_{L(x),λ}."

**Formalization Note.** `D_x` is the concrete circuit `Dx (V λ) x` of Figure 5. The bound (3)
holds with one negligible `μ` uniformly over `x ∈ {0,1}^λ`; "every D_x belongs to C_BQP" is
stated for every choice `x_λ ∈ {0,1}^λ` of one string per length. -/
theorem lemma_4_4_Dx (G : GateSet) (L : Set Str) (V : ℕ → Circ G) (hV : IsDecider G L V)
    (Cb : Bool → ℕ → Circ G) (hCb : IsPadding V Cb) :
    (∀ n (x : Str) (b : Bool), shape (Dx (V n) x) = shape (Cb b n)) ∧
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n (x : Str), x.length = n →
      diamond (chanAs (Dx (V n) x) 1 1) (bitFlip (decide (x ∈ L))) ≤ μ n) ∧
    (∀ xs : ℕ → Str, (∀ n, (xs n).length = n) → InCBQP (fun n => Dx (V n) (xs n))) ∧
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n (x : Str), x.length = n →
      circDist (Dx (V n) x) (Cb (decide (x ∈ L)) n) ≤ μ n) := by sorry

end QiOPoQ
