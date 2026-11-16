-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_lemma_2_3
-- name    : QuantumStateIdentity321.Schur.Supplement.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:56:03.257571+00:00
-- url     : https://prove2.me/theorems/3967ef37-e561-4cb3-ad40-5fdfe655ff77
-- title:
--   Lemma 2.3 — Young's orthogonal basis is a common eigenbasis of the Jucys–Murphy elements, with eigenvalues the contents
-- statement:
--   Let $\lambda\vdash n$ and let $\kappa_\lambda$ be the irreducible representation of $S_n$ on the Specht module $\mathrm{Sp}_\lambda$, written in Young's orthogonal basis $\{|S\rangle:S\in\mathrm{SYT}(\lambda)\}$. For the Jucys–Murphy elements $J_1=0$, $J_i=\sum_{j<i}(j\,i)$ and every $i\in[n]$, $S\in\mathrm{SYT}(\lambda)$,
--
--   $$
--   \kappa_\lambda(J_i)|S\rangle=\mathrm{ct}_S(i)\,|S\rangle ,
--   $$
--
--   where $\mathrm{ct}_S(i)$ is the content (column minus row) of the box of $S$ containing $i$. Consequently Young's orthogonal basis is a common eigenbasis of $\kappa_\lambda(J_1),\dots,\kappa_\lambda(J_n)$.
--
--   The paper quotes this from Pelecanos, Spilecki and Wright [10, Theorem 2.36]; it is the basis of (23), hence of Corollary 4.1.
--
--   **Formalization Note** Young's orthogonal basis is fixed by the Young-orthogonal matrices of the adjacent transpositions (published module P78). The statement asserts that a representation of $S_n$ with these matrices exists and that $\kappa_\lambda$, the representation so determined, satisfies the eigenvalue identity; diagrams are box sets, so a set of boxes that is not a Young diagram has no tableaux and contributes nothing.
--
--   Differences from the source:
--   - encoding: κ_λ, the Specht representation in Young's orthogonal basis → the representation whose adjacent transpositions act by the Young-orthogonal matrices, with its existence stated as a conjunct; reason: Young's orthogonal form determines the representation; the existence conjunct excludes the fallback value
--   - encoding: λ ⊢ n → any finite set of boxes μ; tableaux of shape μ; reason: non-diagrams have no standard tableaux, so the statement is empty for them
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Lemma 2.3, PDF/printed p.8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SchurSampling

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix
open QAlgorithms.Papers.Independent.Intakenext100.P78

attribute [local instance] Classical.propDecidable

/-- Lemma 2.3 ([10, Theorem 2.36]), p.8: for every Young diagram `λ` with `n` boxes there is a
representation `κ_λ` of `S_n` on `ℂ^{SYT(λ)}` in Young's orthogonal form, and for every `i ∈ [n]`
and every standard Young tableau `S` of shape `λ`, `κ_λ(J_i)|S⟩ = ct_S(i)|S⟩`. Hence Young's
orthogonal basis is a common eigenbasis of `κ_λ(J₁), …, κ_λ(Jₙ)`. -/
theorem lemma_2_3 (n : ℕ) (μ : Finset (Fin n × Fin n)) :
    (∃ ρ, IsYoungOrthogonalRep μ ρ) ∧
      ∀ (i : Fin n) (S : YoungEndpointPaths n μ),
        kappaJM μ i *ᵥ Pi.single S (1 : ℂ) =
          ((content S.val i : ℤ) : ℂ) • Pi.single S (1 : ℂ) := by sorry

end QuantumStateIdentity321.Schur.Supplement
