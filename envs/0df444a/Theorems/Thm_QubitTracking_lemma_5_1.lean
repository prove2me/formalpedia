-- Prove2me | Theorems.Thm_QubitTracking_lemma_5_1
-- name    : QubitTracking.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:32:50.323302+00:00
-- url     : https://prove2.me/theorems/28a46eb2-03c5-4fd0-9dac-41a04a2e4eef
-- title:
--   Lemma 5.1 — oracles collapsing to $S$ and to $T$ are indistinguishable from $|S\rangle$: $\mathrm{TD}\le q/2^{(c-b)/2}$
-- statement:
--   Let $a(\lambda)\le b(\lambda)<c(\lambda)\le d(\lambda)$ be polynomials, $W\le\mathbb F_2^d$ a subspace of dimension $c$, and $U(\cdot)$ an efficient isometry with superposition access to a classical oracle. Sample $(S,T)$ uniformly with $T\le W$ of dimension $b$ and $S\le T$ of dimension $a$. Let $\{\mathcal O_S\}$ be oracles with $\mathcal O_S(z)=\bot$ for $z\notin S$, and $\{\mathcal O_{S,T}\}$ oracles with $\mathcal O_{S,T}(z)=\mathcal O_S(z)$ on $S$ and $\bot$ off $T$. Then there is a polynomial $q$ such that, with $|\psi_S\rangle=U^{\mathcal O_S}|S\rangle$, $|\psi_T\rangle=U^{\mathcal O_{S,T}}|S\rangle$ and $|\varphi_S\rangle$, $|\varphi_T\rangle$ the uniform superpositions $\sum_{S,T}|S,T\rangle|\psi_\cdot\rangle$,
--   $$\mathrm{TD}\big(|\varphi_S\rangle\langle\varphi_S|,|\varphi_T\rangle\langle\varphi_T|\big)\le\frac{q}{2^{(c-b)/2}}.$$
--
--   This is the basic indistinguishability step behind the collapsing-oracle extractor of Lemma 7.1.
--
--   Differences from the source:
--   - reading: U(·) any efficient isometry with superposition access to a classical oracle → a polynomial-size circuit of one- and two-qubit unitaries and standard queries acting on the input register and ancillas initialized to |0⟩ (QueryAlg, QAEfficient); reason: the standard circuit model of an efficient oracle isometry
--   - encoding: oracles with outputs and ⊥ → oracles 𝔽₂^d → 𝔽₂^r ∪ {⊥} for an arbitrary length r(λ), the answer encoded in r + 1 qubits; reason: the paper does not fix the output set; any finite one embeds in some 𝔽₂^r
--   - encoding: T ≤ W uniform of dimension b, then S ≤ T uniform of dimension a → (S, T) uniform over all such pairs; reason: every T has the same number of subspaces S, so the two samplings agree
--   - encoding: TD of the pure states |φ_S⟩, |φ_T⟩ → √(1 − |N⁻¹ ∑_{(S,T)} ⟨ψ_S|ψ_T⟩|²); reason: the trace distance of pure unit states, with the |S, T⟩ orthonormal
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), §5 preamble and Lemma 5.1, p.29

import Definitions.Def_QubitTracking_QueryAlg

set_option autoImplicit false

namespace QubitTracking

/-- **Lemma 5.1** (Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time*,
arXiv:2605.30732 (held version, sha256 bf98e5b5…), §5 preamble and Lemma 5.1, p.29). Let
`a(λ) ≤ b(λ) < c(λ) ≤ d(λ)` be polynomials, `W ≤ 𝔽₂^d` a subspace of dimension `c`, `U(·)` any
efficient isometry with superposition access to a classical oracle, and `(S, T)` uniform with
`T ≤ W` of dimension `b` and `S ≤ T` of dimension `a`. Let `{𝒪_S}_S` be any family of oracles with
`𝒪_S(z) = ⊥` for `z ∉ S`, and `{𝒪_{S,T}}_{S,T}` any family with `𝒪_{S,T}(z) = 𝒪_S(z)` for `z ∈ S`
and `𝒪_{S,T}(z) = ⊥` for `z ∉ T`. There is a polynomial `q(λ)` such that, for
`|ψ_S⟩ = U^{𝒪_S}|S⟩`, `|ψ_T⟩ = U^{𝒪_{S,T}}|S⟩`,
`|φ_S⟩ = N^{-1/2} ∑_{S,T} |S, T⟩|ψ_S⟩`, `|φ_T⟩ = N^{-1/2} ∑_{S,T} |S, T⟩|ψ_T⟩`
(`N = (c choose b)₂ (b choose a)₂`),
`TD(|φ_S⟩⟨φ_S|, |φ_T⟩⟨φ_T|) ≤ q / 2^{(c−b)/2}`.

**Formalization Note** Oracles answer in `𝔽₂^r ∪ {⊥}` for an arbitrary length `r(λ)`; an
efficient isometry is a polynomial-size circuit (`QueryAlg`, `QAEfficient`) with any number of
ancillas; the oracle families may depend on `λ`. -/
theorem lemma_5_1 (a b c d : ℕ → ℕ) (ha : PPADSIS.SubexpSIS.PolyBounded a)
    (hb : PPADSIS.SubexpSIS.PolyBounded b) (hc : PPADSIS.SubexpSIS.PolyBounded c)
    (hd : PPADSIS.SubexpSIS.PolyBounded d) (habcd : ∀ l, a l ≤ b l ∧ b l < c l ∧ c l ≤ d l)
    (W : (l : ℕ) → Submodule (ZMod 2) (Bits (Fin (d l))))
    (hW : ∀ l, Module.finrank (ZMod 2) (W l) = c l)
    (k r : ℕ → ℕ) (U : (l : ℕ) → QueryAlg (d l) (k l) (r l)) (hU : QAEfficient U)
    (OS : (l : ℕ) → Submodule (ZMod 2) (Bits (Fin (d l))) → Bits (Fin (d l)) → Option (Bits (Fin (r l))))
    (OST : (l : ℕ) → Submodule (ZMod 2) (Bits (Fin (d l))) → Submodule (ZMod 2) (Bits (Fin (d l))) →
      Bits (Fin (d l)) → Option (Bits (Fin (r l))))
    (hOS : ∀ l S z, z ∉ S → OS l S z = none)
    (hOST : ∀ l S T z, (z ∈ S → OST l S T z = OS l S z) ∧ (z ∉ T → OST l S T z = none)) :
    ∃ q : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded q ∧
      ∀ l, tdPairs (subspacePairs (W l) (a l) (b l))
          (fun S _ => (U l).run (OS l S) (subspaceState S))
          (fun S T => (U l).run (OST l S T) (subspaceState S)) ≤
        (q l : ℝ) / (2 : ℝ) ^ (((c l : ℝ) - (b l : ℝ)) / 2) := by sorry

end QubitTracking
