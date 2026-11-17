-- Prove2me | Theorems.Thm_RelDecoding_Supplement_theorem_4_7
-- name    : RelDecoding.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:15:12.032494+00:00
-- url     : https://prove2.me/theorems/59c6a016-52b5-4218-bbf1-9c657c6d9339
-- title:
--   Theorem 4.7 — $a_i\mapsto b_i$ extends to a $*$-homomorphism iff $A^{\mathsf T}J_{n_A}A=B^{\mathsf T}J_{n_B}B$, $K_A\subseteq K_B$, $\zeta_A=\zeta_B$ on $K_A$
-- statement:
--   Let $a_i=\eta_i^AP_{n_A}(w_i)$ and $b_i=\eta_i^BP_{n_B}(v_i)$, $i=1,\dots,s$, be signed Pauli generators ($\eta_i^L\in\{\pm1\}$, $w_i\in\mathbb F_2^{2n_A}$, $v_i\in\mathbb F_2^{2n_B}$, $P_n(x,z)=i^{x\cdot z}X^xZ^z$), with algebras $\mathcal A=C^*(I,a_1,\dots,a_s)$, $\mathcal B=C^*(I,b_1,\dots,b_s)$, label matrices $A=[w_1\cdots w_s]$, $B=[v_1\cdots v_s]$, relation codes $K_A=\ker A$, $K_B=\ker B$ over $\mathbb F_2$, and ordered products $W_L(c)=a_1^{c_1}\cdots a_s^{c_s}$ (resp. $b$), so that $W_L(c)=\zeta_L(c)I$ for $c\in K_L$. Then the termwise assignment $a_i\mapsto b_i$ extends to a unital $*$-homomorphism $\pi:\mathcal A\to\mathcal B$ if and only if
--   $$A^{\mathsf T}J_{n_A}A=B^{\mathsf T}J_{n_B}B,\qquad K_A\subseteq K_B,\qquad\zeta_A(c)=\zeta_B(c)\ \ (c\in K_A),$$
--   where $J_n=\begin{pmatrix}0&I_n\\I_n&0\end{pmatrix}$.
--
--   The three conditions are: matching pairwise commutation and anticommutation, every scalar relation of the source terms is a relation of the target terms, and these relations carry the same phase. The homomorphism then transports every Hamiltonian polynomial, $\pi(p(H_A))=p(H_B)$.
--
--   Differences from the source:
--   - encoding: aᵢ = ηᵢᴬ P_{n_A}(wᵢ), P_n(x, z) = i^{x·z}X^xZ^z with integer exponent x·z, ηᵢᴸ ∈ {±1}, wᵢ ∈ F₂^{2n_A} → pauliGen ηA wA i = ((ηA i : ℤ) : ℂ) • StabTestMem.weyl (wA i) on Qubits n = Fin n → Bool, ηA i ∈ ℤˣ, labels CutRankSched.Pauli n = (Fin n → ZMod 2) × (Fin n → ZMod 2); the label matrix has rows x then z (Fin n ⊕ Fin n); reason: the published StabTestMem.weyl is the Hermitian Pauli i^{x·z}X^xZ^z with the integer exponent; ℤˣ = {±1}; same operators and labels
--   - encoding: unital ∗-homomorphism π : 𝒜 → ℬ between A = C∗(I_A, a) and B = C∗(I_B, b) → π : genAlg a →⋆ₐ[ℂ] genAlg b (generated ∗-subalgebras of the matrix algebras) with π (gen a i) = gen b i; reason: in finite dimension the generated ∗-subalgebra is the generated C∗-algebra (App. E, p.85)
--   - encoding: ζ_A(c) = ζ_B(c) for c ∈ K_A, where W_L(c) = ζ_L(c) I for c ∈ K_L → ∀ c ∈ K_A, ∀ ζ : ℂ, W_A(c) = ζ • 1 → W_B(c) = ζ • 1; reason: for c ∈ K_A the word W_A(c) is scalar, so ζ_A(c) is the unique ζ with W_A(c) = ζI (the matrix algebras are nonzero); the implication then says W_B(c) = ζ_A(c)I, i.e. ζ_B(c) = ζ_A(c)
-- source:
--   Shang, Stilck França, From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding, arXiv:2609.35101 (held version, sha256 d2be7859…), Theorem 4.7, pp.23–24 (pdf_pages 23–24); = Theorem 1.4, p.9; proof Proposition E.2, pp.86–87

import Mathlib
import Definitions.Def_RelDecoding_markedSpace
import Definitions.Def_CutRankSched_Pauli
import Definitions.Def_StabTestMem_weyl
import Definitions.Def_RelDecoding_Supplement_labelKer
import Definitions.Def_RelDecoding_Supplement_pauliGen

set_option autoImplicit false
open scoped Matrix

namespace RelDecoding.Supplement

open QAlgorithms RelDecoding

/-- **Theorem 4.7 (Pauli homomorphism criterion).** For signed Pauli generators
`aᵢ = ηᵢᴬ P_{n_A}(wᵢ)`, `bᵢ = ηᵢᴮ P_{n_B}(vᵢ)` with label matrices `A = [w₁ ⋯ w_s]`,
`B = [v₁ ⋯ v_s]`, kernels `K_A`, `K_B` over `F₂` and ordered products `W_L(c) = a₁^{c₁}⋯a_s^{c_s}`
(`= ζ_L(c) I` for `c ∈ K_L`), the termwise assignment `aᵢ ↦ bᵢ` extends to a unital
∗-homomorphism `π : A → B` exactly when
`AᵀJ_{n_A}A = BᵀJ_{n_B}B`, `K_A ⊆ K_B`, `ζ_A(c) = ζ_B(c)` (`c ∈ K_A`) (85), with
`J_n = [[0, I_n], [I_n, 0]]` (86).

Shang, Stilck França, *From Simple Sources to Quantum Advantage: Homomorphic Polynomial
Transduction via Relative Decoding*, arXiv:2609.35101 (held version, sha256 d2be7859…),
Theorem 4.7, pp.23–24 (= Theorem 1.4, p.9; proof Proposition E.2, pp.86–87).

**Formalization Note.** `P_n` is the published `StabTestMem.weyl`; `A = genAlg a`, `B = genAlg b`
(generated ∗-subalgebras, equal to the generated C∗-algebras in finite dimension). The phase
condition is encoded as: for `c ∈ K_A`, `W_A(c) = ζI_A` implies `W_B(c) = ζI_B`; since every
`W_A(c)`, `c ∈ K_A`, is scalar and the matrices are nonzero (dimension `2^n ≥ 1`), this is
`ζ_A(c) = ζ_B(c)`. The ordered product uses the representatives `cᵢ ∈ {0, 1}`. -/
theorem theorem_4_7 {nA nB s : ℕ} (wA : Fin s → CutRankSched.Pauli nA) (ηA : Fin s → ℤˣ)
    (wB : Fin s → CutRankSched.Pauli nB) (ηB : Fin s → ℤˣ) :
    (∃ π : genAlg (pauliGen ηA wA) →⋆ₐ[ℂ] genAlg (pauliGen ηB wB),
        ∀ i, π (gen (pauliGen ηA wA) i) = gen (pauliGen ηB wB) i) ↔
      ((pauliLabelMatrix wA)ᵀ * symplecticJ nA * pauliLabelMatrix wA =
          (pauliLabelMatrix wB)ᵀ * symplecticJ nB * pauliLabelMatrix wB ∧
        pauliKer wA ≤ pauliKer wB ∧
        ∀ c ∈ pauliKer wA, ∀ ζ : ℂ, orderedProd (pauliGen ηA wA) c = ζ • 1 →
          orderedProd (pauliGen ηB wB) c = ζ • 1) := by sorry

end RelDecoding.Supplement
