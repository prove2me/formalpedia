-- Prove2me | Theorems.Thm_RelDecoding_Supplement_theorem_4_3
-- name    : RelDecoding.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:14:30.740504+00:00
-- url     : https://prove2.me/theorems/a3f72e28-e9ac-4805-9fd8-6e76efc4a453
-- title:
--   Theorem 4.3 — $d_{\mathrm{rel}}(A\to B)\ge d_{\mathrm{ord}}(B\mid\mathcal A_0)$, strict when minimal relations are inherited
-- statement:
--   Let $\mathcal A_0=C^*(I_0,r_1,\dots,r_s)$, $\mathcal A=C^*(I_A,a_1,\dots,a_s)$ and $\mathcal B$ be finite-dimensional represented algebras with normalized traces $\tau_0,\tau_A,\tau_B$, and let
--   $$\vartheta_A:\mathcal A_0\to\mathcal A,\qquad\pi:\mathcal A\to\mathcal B,\qquad\vartheta_B=\pi\circ\vartheta_A,\qquad\vartheta_A(r_i)=a_i,\ \pi(a_i)=b_i$$
--   be unital $*$-homomorphisms (eq. (49)). The **ordinary distance** is $d_{\mathrm{ord}}(B\mid\mathcal A_0)=d_{\mathrm{rel}}(\mathcal A_0\xrightarrow{\vartheta_B}\mathcal B)$ (eq. (50)). For a marked word $W_0$ in the $r_i$ and their adjoints write $W_A=\vartheta_A(W_0)$, $W_B=\vartheta_B(W_0)$, and assume (eq. (51))
--   $$W_L\notin\mathbb CI_L\implies\tau_L(W_L)=0\qquad(L=0,A,B).$$
--   A **target scalar-word relation relative to $\mathcal A_0$** is a word with $W_B=\lambda I_B$, $\lambda\ne0$, and $W_0\ne\lambda I_0$; it is **inherited from $\mathcal A$** if $W_A=\lambda I_A$. Then
--
--   1. $d_{\mathrm{rel}}(A\to B)\ge d_{\mathrm{ord}}(B\mid\mathcal A_0)$;
--   2. if $d_{\mathrm{ord}}<\infty$ and every target scalar-word relation relative to $\mathcal A_0$ of length $d_{\mathrm{ord}}$ (minimum length) is inherited from $\mathcal A$, the inequality is strict;
--   3. when $\vartheta_A=\mathrm{id}$ (so $\mathcal A_0=\mathcal A$), the ordinary and relative distances coincide.
--
--   This compares ordinary decoding, which must distinguish all low-weight target relations, with relative decoding, which only sees the first relation not already present in the source.
--
--   Differences from the source:
--   - encoding: N_L = dim H_L ≥ 1 for L = 0, A, B (τ_L = Tr/N_L) → [Nonempty n0] [Nonempty nA] [Nonempty nB]; reason: the source divides by N_L; the hypothesis only excludes the undefined case
--   - generalization: A₀ a faithful, relation-free finite-dimensional realization of a generator presentation → A₀ = genAlg r for arbitrary matrices r₁,…,r_s; reason: relation-freeness is used by neither the statement nor the proof; every relation-free A₀ is such a genAlg r, so the Lean statement specializes to the source's
--   - encoding: ϑ_A : A₀ ↠ A, π : A ↠ B, ϑ_B = π ∘ ϑ_A, d_ord(B | A₀) = d_rel(A₀ →^{ϑ_B} B) → ϑA : genAlg r →⋆ₐ[ℂ] genAlg a with ϑA (gen r i) = gen a i; π : genAlg a →⋆ₐ[ℂ] Matrix nB nB ℂ with π (gen a i) = b i; d_ord = relDist r (π.comp ϑA); reason: generated ∗-subalgebras are the generated C∗-algebras in finite dimension (App. E, p.85); same maps and distances
--   - encoding: marked words W₀, W_L ∉ ℂI_L, minimum length → w : List (Fin s × Bool) evaluated by wordEval; ¬∃ μ, W_L = μ • 1; (w.length : ℕ∞) = d_ord; reason: Lean convention for words; 'minimum length' is the length d_ord, the minimum of the relation lengths
--   - encoding: when ϑ_A = id → for every ϑ : genAlg a →⋆ₐ[ℂ] genAlg a with ϑ = StarAlgHom.id, relDist a (π.comp ϑ) = relDist a π; reason: ϑ_A = id forces A₀ = A and rᵢ = aᵢ, so the clause is stated on that source
--   - encoding: distances in ℕ₀ ∪ {+∞}, empty minimum +∞ → values in ℕ∞ defined by sInf, sInf ∅ = ⊤; reason: Lean convention; same values
-- source:
--   Shang, Stilck França, From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding, arXiv:2609.35101 (held version, sha256 d2be7859…), Theorem 4.3, p.19 (pdf_page 19); setting eqs. (49)–(51), pp.18–19

import Mathlib
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_RelDecoding_markedSpace
import Definitions.Def_RelDecoding_relDist

set_option autoImplicit false

namespace RelDecoding.Supplement

open LIDT.MIPStarRE.Quantum RelDecoding

/-- **Theorem 4.3 (Ordinary source versus a quotient source).** Let `A₀ = C∗(I₀, r₁, …, r_s)`,
`A = C∗(I_A, a₁, …, a_s)` and `B` be represented algebras with successive quotients
`ϑ_A : A₀ → A`, `π : A → B(H_B)`, `ϑ_A(rᵢ) = aᵢ`, `π(aᵢ) = bᵢ`, `ϑ_B := π ∘ ϑ_A` (49), and
`d_ord(B | A₀) := d_rel(A₀ →^{ϑ_B} B)` (50). Assume (51): for every marked word `W₀` in the `rᵢ` and
their adjoints, with `W_A = ϑ_A(W₀)`, `W_B = ϑ_B(W₀)`, `W_L ∉ ℂI_L ⟹ τ_L(W_L) = 0` for `L = 0, A, B`.
Then
1. `d_rel(A → B) ≥ d_ord(B | A₀)` (52);
2. if `d_ord < ∞` and every minimum-length target scalar-word relation relative to `A₀` (a word
   with `W_B = λI_B`, `λ ≠ 0`, `W₀ ≠ λI₀`, of length `d_ord`) is inherited from `A` (`W_A = λI_A`),
   then `d_rel(A → B) > d_ord(B | A₀)`;
3. when `ϑ_A = id` (so `A₀ = A`), the ordinary and relative distances coincide.

Shang, Stilck França, *From Simple Sources to Quantum Advantage: Homomorphic Polynomial
Transduction via Relative Decoding*, arXiv:2609.35101 (held version, sha256 d2be7859…),
Theorem 4.3, p.19 (setting eqs. (49)–(51), pp.18–19).

**Formalization Note.** The three algebras are `genAlg r`, `genAlg a` and the range of `π` in
`Matrix nB nB ℂ`, as for the published `relDist`; `d_ord = relDist r (π.comp ϑA)`. Marked words are
`List (Fin s × Bool)` evaluated by `wordEval` (`true` = adjoint); "length" is the list length.
`[Nonempty]` on the three index types records `N_L = dim H_L ≥ 1`, presupposed by `τ_L = Tr/N_L`.
The relation-freeness of `A₀` is not assumed. -/
theorem theorem_4_3 {n0 nA nB : Type*} [Fintype n0] [DecidableEq n0] [Fintype nA]
    [DecidableEq nA] [Fintype nB] [DecidableEq nB] [Nonempty n0] [Nonempty nA] [Nonempty nB]
    {s : ℕ} (r : Fin s → Matrix n0 n0 ℂ) (a : Fin s → Matrix nA nA ℂ)
    (b : Fin s → Matrix nB nB ℂ) (ϑA : genAlg r →⋆ₐ[ℂ] genAlg a)
    (hϑ : ∀ i, ϑA (gen r i) = gen a i) (π : genAlg a →⋆ₐ[ℂ] Matrix nB nB ℂ)
    (hπ : ∀ i, π (gen a i) = b i)
    (h51 : ∀ w : List (Fin s × Bool),
      ((¬ ∃ μ : ℂ, (wordEval r w : Matrix n0 n0 ℂ) = μ • 1) →
          normalizedTrace (wordEval r w : Matrix n0 n0 ℂ) = 0) ∧
        ((¬ ∃ μ : ℂ, (ϑA (wordEval r w) : Matrix nA nA ℂ) = μ • 1) →
          normalizedTrace (ϑA (wordEval r w) : Matrix nA nA ℂ) = 0) ∧
        ((¬ ∃ μ : ℂ, π (ϑA (wordEval r w)) = μ • 1) →
          normalizedTrace (π (ϑA (wordEval r w))) = 0)) :
    relDist r (π.comp ϑA) ≤ relDist a π ∧
      (relDist r (π.comp ϑA) < ⊤ →
        (∀ (w : List (Fin s × Bool)) (lam : ℂ), lam ≠ 0 →
            π (ϑA (wordEval r w)) = lam • 1 →
            (wordEval r w : Matrix n0 n0 ℂ) ≠ lam • 1 →
            (w.length : ℕ∞) = relDist r (π.comp ϑA) →
            (ϑA (wordEval r w) : Matrix nA nA ℂ) = lam • 1) →
          relDist r (π.comp ϑA) < relDist a π) ∧
      (∀ ϑ : genAlg a →⋆ₐ[ℂ] genAlg a, ϑ = StarAlgHom.id ℂ (genAlg a) →
        relDist a (π.comp ϑ) = relDist a π) := by sorry

end RelDecoding.Supplement
