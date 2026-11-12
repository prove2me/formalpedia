-- Prove2me | Theorems.Thm_QuantumKtSoI_lemma_3_3
-- name    : QuantumKtSoI.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:12.222624+00:00
-- url     : https://prove2.me/theorems/2f1f15a3-4175-4244-9ca9-629cc18c32cc
-- title:
--   Lemma 3.3 — record law
-- statement:
--   Fix a machine $M$ of Definition 3.1 and an input $x$. Write $S$ for the step operator, $\Pi_r$ for the projector onto the configurations with record $r$, and $\psi_\rho$ for the branch vector of a record sequence $\rho$.
--   1. For every finite-support vector $\phi$ and every record $r$, $\|S\Pi_r\phi\|=\|\Pi_r\phi\|$.
--   2. For every finite-support vector $\phi$, $\sum_r\|S\Pi_r\phi\|^2=\|\phi\|^2$; consequently
--   $$\sum_{\rho\in R^s}\|\psi_\rho\|^2=1\ \text{ for every } s,\qquad \sum_{\nu\in R^u}\|\psi_{\rho\nu}\|^2=\|\psi_\rho\|^2\ \text{ for every } \rho,u.$$
--   3. If $\psi_\rho\ne0$, all configurations in its support have the same state, the same head positions and the same contents on every classical tape.
--
--   The record law makes the output distribution of Definition 3.4 a probability distribution and makes the state and output of a branch well defined.
--
--   Differences from the source:
--   - generalization: finite-support vectors over the paper's configurations (finitely many nonblank cells, alphabet symbols) → finite-support vectors over all triples (state, contents ℤ → Sym, heads); reason: the paper's configurations are among them, so (i)–(ii) specialize to the source
--   - encoding: ‖SΠ_rϕ‖ = ‖Π_rϕ‖ and sums of ‖·‖² → equalities of squared norms sqNorm; reason: norms are nonnegative, so equal squares are equal norms
--   - encoding: sums over all records R and all record sequences Rˢ, Rᵘ → sums over φ.support.image record, recSeqs x s, extSeqs x ρ u; reason: every record or sequence outside these finite sets contributes a zero vector
--   - encoding: per-tape finite alphabets and companions of Definition 3.1 (pp.20, 23, 26) → alphabets are finite subsets of one countable symbol type Sym; the companion of a qubit tape is designated (least index for coded machines, the copy of the component's companion for constructed machines); reason: a renaming of alphabet symbols; the companion choices are the paper's own (p.23, p.26)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Lemma 3.3, p.21

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI

/-- **Lemma 3.3** (Record law; Myrisiotis, *Failure of Symmetry of Information for Quantum
Computations*, STOC 2027 submission, held version sha256 6616571c…, p.21). Fix a machine of
Definition 3.1 and an input `x`.
(i) For every vector `ϕ` with finite support and every record `r`, `‖SΠ_r ϕ‖ = ‖Π_r ϕ‖`.
(ii) For every finite-support vector `ϕ`, `Σ_r ‖SΠ_r ϕ‖² = ‖ϕ‖²`; consequently
`Σ_{ρ ∈ Rˢ} ‖ψ_ρ‖² = 1` for every `s`, and `Σ_{ν ∈ Rᵘ} ‖ψ_{ρν}‖² = ‖ψ_ρ‖²` for every `ρ` and `u`.
(iii) If `ψ_ρ ≠ 0`, then all basis configurations in its support have the same state, the same
head positions, and the same contents on every classical tape.

**Formalization Note** Norms are compared through their squares `sqNorm`. The sums over records
and record sequences run over the finite sets outside which every term vanishes
(`φ.support.image record`, `recSeqs`, `extSeqs`). Configurations are all triples
(state, contents `T → ℤ → Sym`, heads), including ones with infinitely many written cells or
symbols outside an alphabet, so (i) and (ii) quantify over more vectors than the paper's. -/
theorem lemma_3_3 (M : Machine) (hM : M.Valid) (x : List Bool) :
    (∀ φ : M.Config →₀ ℂ, ∀ r : M.Record,
        M.sqNorm (M.step (M.proj r φ)) = M.sqNorm (M.proj r φ)) ∧
      (∀ φ : M.Config →₀ ℂ,
        ∑ r ∈ φ.support.image Machine.Config.record, M.sqNorm (M.step (M.proj r φ)) =
          M.sqNorm φ) ∧
      (∀ s : ℕ, ∑ ρ ∈ M.recSeqs x s, M.sqNorm (M.branch x ρ) = 1) ∧
      (∀ (ρ : List M.Record) (u : ℕ),
        ∑ ν ∈ M.extSeqs x ρ u, M.sqNorm (M.branch x (ρ ++ ν)) = M.sqNorm (M.branch x ρ)) ∧
      ∀ ρ : List M.Record, M.branch x ρ ≠ 0 →
        ∀ C ∈ (M.branch x ρ).support, ∀ C' ∈ (M.branch x ρ).support,
          C.state = C'.state ∧ C.head = C'.head ∧
            ∀ t, M.kind t = TapeKind.classical → C.cont t = C'.cont t := by sorry

end QuantumKtSoI
