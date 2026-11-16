-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_corollary_4_1
-- name    : QuantumStateIdentity321.Schur.Supplement.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:56:50.309215+00:00
-- url     : https://prove2.me/theorems/cff50ca4-ccaa-46c3-9f07-0f397cc48079
-- title:
--   Corollary 4.1 — $P(J_i)=\sum_{\lambda,S}\mathrm{ct}_S(i)M_{\lambda,S}$: the Schur measurement jointly resolves the Jucys–Murphy eigenvalues
-- statement:
--   Let $n\ge2$, $d\ge2$, and let $M_{\lambda,S}=U_{\mathrm{Schur}}^\dagger(|\lambda\rangle\langle\lambda|\otimes|S\rangle\langle S|\otimes I)U_{\mathrm{Schur}}$ be the measurement (22) of the Young-diagram and tableau labels after the Schur transform, for $\lambda\vdash n$ with $\ell(\lambda)\le d$ and $S\in\mathrm{SYT}(\lambda)$. Then a Schur transform exists, $\{M_{\lambda,S}\}_{\lambda,S}$ is a projective measurement (orthogonal projections, pairwise orthogonal, summing to $I$), and for every $i\in[n]$
--
--   $$
--   P(J_i)=\sum_{\substack{\lambda\vdash n\\ \ell(\lambda)\le d}}\ \sum_{S\in\mathrm{SYT}(\lambda)}\mathrm{ct}_S(i)\,M_{\lambda,S},
--   $$
--
--   where $P(J_i)=\sum_{j<i}P_{ij}$ is the sum of the SWAP operators of tensor factors $j<i$ with factor $i$. Therefore the measurement jointly resolves the eigenvalues of the commuting Jucys–Murphy operators, and an outcome $(\lambda,S)$ determines the eigenvalue $\mathrm{ct}_S(i)$ of every $J_i$.
--
--   This is the measurement used in each round of Algorithm 3; Lemma 4.2 turns it into an estimator of fidelity sums.
--
--   **Formalization Note** An outcome is a standard tableau $S$ with at most $d$ rows, $\lambda$ being its shape. The Schur transform is required to intertwine the $S_n$ action as in (8); the $GL(d)$ part of (8) does not change $M_{\lambda,S}$.
--
--   Differences from the source:
--   - encoding: U_Schur of (8), intertwining P(π)Q_d(M) with ⊕ |λ⟩⟨λ| ⊗ κ_λ(π) ⊗ ν_λ^d(M) → a unitary intertwining P(π) with ⊕ κ_λ(π) ⊗ I (S_n part only); reason: M_{λ,S} depends only on the S_n isotypic and Young-basis structure; every U_Schur of (8) is such a unitary
--   - encoding: existence of U_Schur (Schur–Weyl duality, p.7), presupposed by (22) → Nonempty (SchurTransform n d) as a conjunct; reason: M_{λ,S} is defined from a chosen transform; the conjunct excludes the fallback value
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Corollary 4.1, PDF/printed p.15, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SchurSampling

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

attribute [local instance] Classical.propDecidable

/-- Corollary 4.1 (joint spectral measurement of the Jucys–Murphy operators), p.15, for `n ≥ 2`
and `d ≥ 2`: a Schur transform exists, the operators `M_{λ,S}` of (22) (`λ ⊢ n`, `ℓ(λ) ≤ d`,
`S ∈ SYT(λ)`) form a projective measurement (orthogonal projections, pairwise orthogonal, summing
to `I`), and for every `i ∈ [n]`, `P(J_i) = Σ_{λ, S} ct_S(i) M_{λ,S}`, so an outcome `(λ, S)`
determines the eigenvalue `ct_S(i)` of every `J_i`. -/
theorem corollary_4_1 (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    Nonempty (SchurTransform n d) ∧
      (∀ S : SchurOutcome n d, (schurProj (d := d) S.val).IsHermitian ∧
        schurProj (d := d) S.val * schurProj (d := d) S.val = schurProj (d := d) S.val) ∧
      (∀ S T : SchurOutcome n d, S ≠ T →
        schurProj (d := d) S.val * schurProj (d := d) T.val = 0) ∧
      (∑ S : SchurOutcome n d, schurProj (d := d) S.val = 1) ∧
      ∀ i : Fin n, jmOp (d := d) i =
        ∑ S : SchurOutcome n d, ((content S.val i : ℤ) : ℂ) • schurProj (d := d) S.val := by sorry

end QuantumStateIdentity321.Schur.Supplement
