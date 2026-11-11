-- Prove2me | Theorems.Thm_PetzMix_lemma_4_2
-- name    : PetzMix.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:16:11.546174+00:00
-- url     : https://prove2.me/theorems/51942cc1-df05-4cde-afb2-15bfd76cf17e
-- title:
--   Lemma 4.2 — Petz-amplitude factorization
-- statement:
--   Let $B$ be a set of sites and $\tau_B$ a full-rank state on $B$, with product conditional expectation $E_B$ and conditional Petz amplitude $Q_B=\sigma_\beta^{1/2}(\tau_B^{-1/2}\otimes\sigma_{\beta,B^c}^{-1/2})$ (Definition 4.1). Then for every operator $A$,
--   $$
--   \Phi_B^\dagger(A)=E_B\big(Q_B^\dagger AQ_B\big),\qquad E_B\big(Q_B^\dagger Q_B\big)=I .
--   $$
--
--   The factorization separates the replacement of the block by $\tau_B$ from the correction $Q_B$, which carries the coupling of $B$ to its complement.
--
--   **Formalization Note** $\tau_B$ enters as $T=\tau_B\otimes I_{B^c}$.
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - reading: two-site interactions h ∈ B(ℂ^d ⊗ ℂ^d) with ‖h‖ ≤ 1 → Hermitian bonds (IsPeriodicNN) with opNorm ≤ 1; reason: H is called a Hamiltonian and σ_β is a state only for Hermitian H
--   - encoding: the periodic chain Λn = ℤ/nℤ and operators on regions → sites Fin n, operators QDSGibbs.Op, region operators as A ⊗ I (SupportedOn); reason: Lean convention; same instances
--   - encoding: a full-rank state τ_B on B → T = τ_B ⊗ I_{B^c} with IsBlockRef B T (positive definite, trivial on B^c, ptr B T = 1); reason: the same objects, re-embedded on the full chain
--   - generalization: a block B and an observable A → every finite set of sites B and every operator A; reason: both identities hold verbatim in that generality; the paper's blocks and observables are among them
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Lemma 4.2, (57), p.20; Definition 4.1, (55)–(56), p.19

import Mathlib
import Definitions.Def_PetzMix_petzAmp
import Definitions.Def_QDSGibbs_IsChannel

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Lemma 4.2 (Petz-amplitude factorization)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Lemma 4.2, (57), p.20; Definition 4.1,
(55)–(56), p.19). For every observable `A`, `Φ_B†(A) = E_B(Q_B† A Q_B)` and `E_B(Q_B† Q_B) = I`.

**Formalization Note** `τ_B` is any full-rank state on `B`, represented by `T = τ_B ⊗ I_{B^c}`
(`IsBlockRef B T`); `E_B` is `condExp B T`, `Q_B` is `petzAmp σ_β B T`, `Φ_B†` is the public
`QDSGibbs.heisAdj`. Stated for every finite set `B` and every operator `A`. -/
theorem lemma_4_2 (n d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 ≤ β) (h : Fin n → ChainOp n d)
    (hh : IsPeriodicNN h) (hnorm : ∀ i, opNorm (h i) ≤ 1) (B : Finset (Fin n)) (T : ChainOp n d)
    (hT : IsBlockRef B T) :
    (∀ A : ChainOp n d,
      heisAdj (petzUpdate (gibbs β (∑ i, h i)) B) A =
        condExp B T ((petzAmp (gibbs β (∑ i, h i)) B T)ᴴ * A * petzAmp (gibbs β (∑ i, h i)) B T)) ∧
    condExp B T ((petzAmp (gibbs β (∑ i, h i)) B T)ᴴ * petzAmp (gibbs β (∑ i, h i)) B T) = 1 := by sorry

end PetzMix
