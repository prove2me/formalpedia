-- Prove2me | Theorems.Thm_RelDecoding_Supplement_theorem_6_1
-- name    : RelDecoding.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:16:20.603336+00:00
-- url     : https://prove2.me/theorems/0fc6ac69-4c9a-452a-858a-1818e17f4f4c
-- title:
--   Theorem 6.1 — Majorana criterion: surjective $*$-homomorphism iff $A^{\mathsf T}A=B^{\mathsf T}B$, $K_A\subseteq K_B$, $\zeta_A=\zeta_B$; then $\pi(p(H_A))=p(H_B)$
-- statement:
--   For $L\in\{A,B\}$ let $\gamma_{L,1},\dots,\gamma_{L,2n_L}$ be the Majorana operators of the full Fock space of $n_L$ modes and $\Gamma_L(u)=i^{|u|(|u|-1)/2}\prod_j\gamma_{L,j}^{u_j}$ (increasing order) the Hermitian Majorana monomials. Let $a_i=\eta_i^A\Gamma_A(w_i)$, $b_i=\eta_i^B\Gamma_B(v_i)$, $i=1,\dots,s$, with $\eta_i^L\in\{\pm1\}$ and nonzero even-weight labels $w_i\in\mathbb F_2^{2n_A}$, $v_i\in\mathbb F_2^{2n_B}$; let $\mathcal A=C^*(I_A,a_1,\dots,a_s)$, $\mathcal B=C^*(I_B,b_1,\dots,b_s)$, $A=[w_1\cdots w_s]$, $B=[v_1\cdots v_s]$, $K_A=\ker A$, $K_B=\ker B$ over $\mathbb F_2$, and $W_L(c)=a_1^{c_1}\cdots a_s^{c_s}$ (resp. $b$), $W_L(c)=\zeta_L(c)I_L$ for $c\in K_L$.
--
--   1. The assignment $a_i\mapsto b_i$ extends to a surjective unital $*$-homomorphism $\pi:\mathcal A\to\mathcal B$ if and only if
--   $$A^{\mathsf T}A=B^{\mathsf T}B,\qquad K_A\subseteq K_B,\qquad\zeta_A(c)=\zeta_B(c)\ \ (c\in K_A).$$
--   2. For the matched Hamiltonians $H_A=E_cI_A+\sum_i\lambda_ia_i$, $H_B=E_cI_B+\sum_i\lambda_ib_i$ with $\lambda_i>0$ and $E_c\in\mathbb R$, every such map satisfies
--   $$\pi(H_A)=H_B,\qquad\pi(p(H_A))=p(H_B)$$
--   for every polynomial $p$.
--
--   This is the fermionic analogue of the Pauli criterion: it decides when polynomial filters of a parity-preserving source Hamiltonian can be transported to a target Hamiltonian with the same coefficient magnitudes.
--
--   Differences from the source:
--   - encoding: Majoranas γ_{L,j} of the full Fock space of n_L modes, from any f_{L,j} satisfying (136) → the Jordan–Wigner matrices of eq. (167), the published FermiCap.Gaussian.majorana (0-based index p ↦ γ_{p+1}), on Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ; labels Fin (2n) → ZMod 2; reason: the source gives these matrices itself (eq. (167)); every CAR family on ℂ^{2^n} is unitarily equivalent to them, and the statement is invariant under a unitary change of basis on either side
--   - encoding: unital ∗-homomorphism π : 𝒜 → ℬ between A = C∗(I_A, a) and B = C∗(I_B, b), surjective → π : genAlg a →⋆ₐ[ℂ] genAlg b (generated ∗-subalgebras of the matrix algebras) with π (gen a i) = gen b i; reason: in finite dimension the generated ∗-subalgebra is the generated C∗-algebra (App. E, p.85)
--   - encoding: ζ_A(c) = ζ_B(c) for c ∈ K_A, where W_L(c) = ζ_L(c) I for c ∈ K_L → ∀ c ∈ K_A, ∀ ζ : ℂ, W_A(c) = ζ • 1 → W_B(c) = ζ • 1; reason: for c ∈ K_A the word W_A(c) is scalar, so ζ_A(c) is the unique ζ with W_A(c) = ζI (the matrix algebras are nonzero); the implication then says W_B(c) = ζ_A(c)I, i.e. ζ_B(c) = ζ_A(c)
--   - encoding: π(H_A) = H_B, π(p(H_A)) = p(H_B) for every polynomial p → H_A as the element E_c • 1 + Σ λᵢ • gen a i of A; equalities of matrices after coercion; p : Polynomial ℂ evaluated by Polynomial.aeval; reason: complex polynomials are the source's polynomials in operators; same identities
-- source:
--   Shang, Stilck França, From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding, arXiv:2609.35101 (held version, sha256 d2be7859…), Theorem 6.1, p.35 (pdf_page 35); setting eqs. (136), (140)–(141), (151)–(154), pp.33–35; proof Proposition E.3, pp.88–89

import Mathlib
import Definitions.Def_RelDecoding_markedSpace
import Definitions.Def_FermiCap_Gaussian_Majorana
import Definitions.Def_RelDecoding_Supplement_labelKer
import Definitions.Def_RelDecoding_Supplement_majoranaGen

set_option autoImplicit false
open scoped Matrix

namespace RelDecoding.Supplement

open FermiCap.Gaussian RelDecoding

/-- **Theorem 6.1 (Homomorphisms between Majorana-generated algebras).** For signed Majorana
generators `aᵢ = ηᵢᴬ Γ_A(wᵢ)`, `bᵢ = ηᵢᴮ Γ_B(vᵢ)` with nonzero even-weight labels `wᵢ ∈ F₂^{2n_A}`,
`vᵢ ∈ F₂^{2n_B}`, label matrices `A = [w₁ ⋯ w_s]`, `B = [v₁ ⋯ v_s]`, kernels `K_A`, `K_B` over `F₂`
and ordered products `W_L(c) = a₁^{c₁}⋯a_s^{c_s}` (`= ζ_L(c) I_L` for `c ∈ K_L`), the assignment
`aᵢ ↦ bᵢ` extends to a surjective unital ∗-homomorphism `π : A → B` if and only if
`AᵀA = BᵀB`, `K_A ⊆ K_B`, `ζ_A(c) = ζ_B(c)` (`c ∈ K_A`) (155). For the matched Hamiltonians
`H_A = E_c I_A + Σᵢ λᵢ aᵢ`, `H_B = E_c I_B + Σᵢ λᵢ bᵢ`, `λᵢ > 0`, `E_c ∈ ℝ` (151), such a map satisfies
`π(H_A) = H_B` and `π(p(H_A)) = p(H_B)` for every polynomial `p` (156).

Shang, Stilck França, *From Simple Sources to Quantum Advantage: Homomorphic Polynomial
Transduction via Relative Decoding*, arXiv:2609.35101 (held version, sha256 d2be7859…),
Theorem 6.1, p.35 (setting eqs. (136), (140)–(141), (151)–(154), pp.33–35; proof Proposition E.3,
pp.88–89).

**Formalization Note.** `Γ_L` is `majoranaMonomial` on the Jordan–Wigner Majoranas (167) (the
published `FermiCap.Gaussian.majorana`); `A = genAlg a`, `B = genAlg b`, and `π : A →⋆ₐ[ℂ] B` with
`π (gen a i) = gen b i` and `Function.Surjective π`. The phase condition is encoded as: for
`c ∈ K_A`, `W_A(c) = ζI_A` implies `W_B(c) = ζI_B`. Polynomials are complex, `p ∈ ℂ[X]`, evaluated
by `Polynomial.aeval` in `A` and in `Matrix`. -/
theorem theorem_6_1 {nA nB s : ℕ} (wA : Fin s → Fin (2 * nA) → ZMod 2) (ηA : Fin s → ℤˣ)
    (wB : Fin s → Fin (2 * nB) → ZMod 2) (ηB : Fin s → ℤˣ)
    (hwA : ∀ i, wA i ≠ 0 ∧ Even (hammingNorm (wA i)))
    (hwB : ∀ i, wB i ≠ 0 ∧ Even (hammingNorm (wB i))) :
    ((∃ π : genAlg (majoranaGen ηA wA) →⋆ₐ[ℂ] genAlg (majoranaGen ηB wB),
        (∀ i, π (gen (majoranaGen ηA wA) i) = gen (majoranaGen ηB wB) i) ∧
          Function.Surjective π) ↔
      ((labelMatrix wA)ᵀ * labelMatrix wA = (labelMatrix wB)ᵀ * labelMatrix wB ∧
        labelKer wA ≤ labelKer wB ∧
        ∀ c ∈ labelKer wA, ∀ ζ : ℂ, orderedProd (majoranaGen ηA wA) c = ζ • 1 →
          orderedProd (majoranaGen ηB wB) c = ζ • 1)) ∧
    ∀ π : genAlg (majoranaGen ηA wA) →⋆ₐ[ℂ] genAlg (majoranaGen ηB wB),
      (∀ i, π (gen (majoranaGen ηA wA) i) = gen (majoranaGen ηB wB) i) →
      Function.Surjective π →
      ∀ (Ec : ℝ) (lam : Fin s → ℝ), (∀ i, 0 < lam i) →
        ((π ((Ec : ℂ) • (1 : genAlg (majoranaGen ηA wA)) +
              ∑ i, ((lam i : ℝ) : ℂ) • gen (majoranaGen ηA wA) i) : Op nB) =
            (Ec : ℂ) • (1 : Op nB) + ∑ i, ((lam i : ℝ) : ℂ) • majoranaGen ηB wB i) ∧
        ∀ p : Polynomial ℂ,
          ((π (Polynomial.aeval ((Ec : ℂ) • (1 : genAlg (majoranaGen ηA wA)) +
                ∑ i, ((lam i : ℝ) : ℂ) • gen (majoranaGen ηA wA) i) p) : Op nB) =
            Polynomial.aeval ((Ec : ℂ) • (1 : Op nB) +
              ∑ i, ((lam i : ℝ) : ℂ) • majoranaGen ηB wB i) p) := by sorry

end RelDecoding.Supplement
