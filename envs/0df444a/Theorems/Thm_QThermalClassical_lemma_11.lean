-- Prove2me | Theorems.Thm_QThermalClassical_lemma_11
-- name    : QThermalClassical.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:47.447984+00:00
-- url     : https://prove2.me/theorems/ce1bb49f-12bf-46f6-b278-7e63928f018e
-- title:
--   Lemma 11 — pinning validity
-- statement:
--   Consider one iteration of Algorithm 1 (ITERATIVE PINNING) for a Pauli Hamiltonian $H$, unpinned sites $S$ and configuration $\chi$.
--   1. The iteration can start: if $A(S)\neq\emptyset$ there is an admissible choice of $a^*$ (lines 3–6).
--   2. For every admissible $a^*$, every pair of sampled outcomes and every branch $J$, the new site set $\hat S=S\setminus\mathrm{supp}(P_{a^*})$ is a proper subset of $S$, so the loop terminates.
--   3. If $u_S(X_i)=\emptyset$ for $i\in[l-1]$, then $u_{\hat S}(\hat X_i)=\emptyset$ for $i\in[\hat l-1]$.
--   4. If $\chi$ is valid (disjoint Hermitian monomials) and satisfies the invariant of item 3, and the two outcomes are Pauli products up to a phase whose term lists consist of terms in $A(S)$ (the form of the sampling primitive), then the new configuration $\hat\chi$ is valid.
--
--   A factor whose update gives $\hat X=0$ is reset to $(0,I)$, which is line 26 of the algorithm.
--
--   Differences from the source:
--   - encoding: one loop iteration of Algorithm 1 with its nondeterministic choice of $a^*$ and random samples → a function of $a^*$, the two outcomes and $J$, quantified over all admissible $a^*$ and all values; reason: the lemma is claimed for every run
--   - reading: "Every iteration of the algorithm completes" → an admissible $a^*$ exists when $A(S)\neq\emptyset$, and $\hat S\subsetneq S$; reason: the proof's content: $a^*\cap S\neq\emptyset$, so $S$ strictly shrinks and the loop terminates
--   - reading: "produces a valid configuration if the input is a valid configuration" → valid and invariant input, outcomes of the primitive's form ⟹ valid output; reason: the proof uses the invariant for disjointness ("the invariant guarantees the final monomial is disjoint from the earlier monomials") and that the $E_i$ are products of terms in $A(S)$; without the invariant a valid configuration whose earlier monomial meets $S$ can lose disjointness; the invariant holds at every iteration of the algorithm
--   - encoding: the branch probability parameter $q$ → an arbitrary real $q$; reason: validity does not depend on the coefficients
--   - encoding: a Pauli Hamiltonian $H=\sum_{a\in A}c_aP_a$ with distinct non-identity Pauli strings → a coefficient function $c$ on Pauli words with $c(I)=0$, $A=\{P: c_P\neq 0\}$; reason: distinctness is automatic and words with coefficient $0$ change neither $H$ nor any condition; no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 11, p.29; Algorithm 1, p.27

import Mathlib
import Definitions.Def_QThermalClassical_pinStep

set_option autoImplicit false

namespace QThermalClassical

/-- **Lemma 11 (Pinning validity).** One iteration of Algorithm 1 completes and maps a valid
configuration to a valid configuration: if `A(S) ≠ ∅` an admissible `a*` exists; for every
admissible `a*`, every pair of outcomes of the sampling primitive (Pauli products up to a
phase whose term lists consist of terms in `A(S)`) and every branch `J`, the new site set
`Ŝ` is a proper subset of `S` (so the loop terminates), the new configuration `χ̂` is valid
(disjoint Hermitian monomials), and if `u_S(X_i) = ∅` for `i ∈ [l − 1]` then
`u_Ŝ(X̂_i) = ∅` for `i ∈ [l̂ − 1]`. The discarding of a factor with `X̂ = 0` is line 26 of the
algorithm, built into `pinStep`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 11, p.29; Algorithm 1, p.27.

**Formalization Note.** Validity of the output is proved for an input in the state Algorithm 1
is in at every iteration, i.e. valid *and* satisfying the invariant: the proof uses the
invariant for disjointness ("the invariant guarantees the final monomial is disjoint from the
earlier monomials"), and without it a valid configuration whose earlier monomial meets `S` can
lose disjointness. `H = Σ_P c_P P` is a Pauli Hamiltonian, so it has no identity term
(`c (fun _ => 0) = 0`, eq. (5)). The probability parameter `q` plays no role in validity and
is arbitrary. -/
theorem lemma_11 {Q : Type} [Fintype Q] [DecidableEq Q] (c : PauliWord Q → ℝ)
    (hc0 : c (fun _ => 0) = 0) (q : ℝ) (S : Finset Q) (χ : Config Q) :
    ((termsIn c S).Nonempty → ∃ a, IsAdmissible c S χ a) ∧
    ∀ a, IsAdmissible c S χ a → ∀ (o₁ o₂ : Outcome Q) (J : Fin 7),
      (pinStep q S χ a o₁ o₂ J).1 ⊂ S ∧
      (PinInvariant S χ →
        PinInvariant (pinStep q S χ a o₁ o₂ J).1 (pinStep q S χ a o₁ o₂ J).2) ∧
      (IsValidConfig χ → PinInvariant S χ →
        IsPauliProd o₁.C o₁.E → (∀ b ∈ o₁.C, b ∈ termsIn c S) →
        IsPauliProd o₂.C o₂.E → (∀ b ∈ o₂.C, b ∈ termsIn c S) →
        IsValidConfig (pinStep q S χ a o₁ o₂ J).2) := by sorry

end QThermalClassical
