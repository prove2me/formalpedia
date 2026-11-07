-- Prove2me | Theorems.Thm_ShadowBootstrap_theorem_5_1
-- name    : ShadowBootstrap.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:08.557006+00:00
-- url     : https://prove2.me/theorems/de75f5f6-a33b-43d0-b9cd-7668276ce961
-- title:
--   Theorem 5.1 — initialization: $\Pr[|\langle\psi|\sigma_0\rangle|^2 \ge 1/2] \ge 11/12$ with $O(d)$ copies, $O(n^3)$ bases, depth $O(\log n)$
-- statement:
--   There are constants $K$ and $C$ such that for every $n$, with the suffix ensembles $E_\ell$ of Lemma A.2 and the choices
--   $$N_\ell := \lceil Kn^2\rceil,\qquad S_\ell := \Big\lceil\frac{K d^{2/3}2^{\ell/3}}{N_\ell}\Big\rceil,\qquad \ell = 0, \dots, n-1,\ d = 2^n,$$
--   the following hold.
--
--   1. $\sum_{\ell=0}^{n-1}N_\ell S_\ell \le C\,d$ and $\sum_{\ell=0}^{n-1}N_\ell \le C\,n^3$.
--   2. Every unitary of every $E_\ell$ is, up to a global phase, realized by a circuit over $\{H, S, CX\}$ of depth at most $C(\lfloor\log_2 n\rfloor + 1)$.
--   3. For every rule choosing normalized top eigenvectors, the reconstruction of §5.3–5.5 outputs a unit vector $|\sigma_0\rangle$ on every data, and for every unit vector $|\psi\rangle$,
--   $$\Pr\Big[|\langle\psi|\sigma_0\rangle|^2 \ge \tfrac12\Big] \ge \tfrac{11}{12},$$
--   the probability being over the independent levels' bases and outcomes.
--
--   The protocol is nonadaptive and single-copy: all bases and shot counts are fixed before any outcome is observed.
--
--   Differences from the source:
--   - generalization: there are choices of N_ℓ and S_ℓ → the proof's and Algorithm 1's choices N_ℓ = ⌈Kn²⌉, S_ℓ = ⌈Kd^{2/3}2^{ℓ/3}/N_ℓ⌉ with one integer K; reason: the statement for specific choices implies existence
--   - reading: under the measurement assumptions above → the suffix ensembles of Lemma A.2; reason: Lemma 5.4 refers to them
--   - reading: each measurement has Clifford depth O(log n) → circuits over {H, S, CX} with valid layers of depth ≤ C(⌊log₂ n⌋ + 1) realizing every unitary up to a global phase; reason: the level measurement I ⊗ U has the same depth
--   - generalization: outputs a unit vector → a unit vector on every histogram data, for every eigenvector rule; reason: the paper normalizes by construction
--   - generalization: an n-qubit state (n ≥ 1 implicit) → every n, including n = 0; reason: at n = 0 there are no levels, the output is the leaf value 1 and every clause holds
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Theorem 5.1, p.16, and its proof, pp.22–23

import Mathlib
import Definitions.Def_ShadowBootstrap_alg1Data

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Theorem 5.1, p.16 (initialization): under the measurement assumptions (Lemma 5.4), there are
choices of `N_ℓ` and `S_ℓ` such that the reconstruction outputs a unit vector `|σ₀⟩` with
`Pr[|⟨ψ|σ₀⟩|² ≥ 1/2] ≥ 11/12`; the protocol is nonadaptive and single-copy, with
`Σ_ℓ N_ℓS_ℓ = O(d)` and `Σ_ℓ N_ℓ = O(n³)`, and each measurement has Clifford depth `O(log n)`.

**Formalization Note** The choices are the proof's (p.22) and Algorithm 1's, `N_ℓ := ⌈Kn²⌉` and
`S_ℓ := ⌈K d^{2/3} 2^{ℓ/3}/N_ℓ⌉` for one constant `K` (taken integral); stated for them, the theorem
implies the printed "there are choices". The ensembles are those of Lemma A.2 (`suffixEnsemble`),
level `ℓ` using `j = n − ℓ` suffix qubits, and the depth clause is about circuits over `{H, S, CX}`
realizing their unitaries up to a global phase (the level-`ℓ` measurement `I_{2^ℓ} ⊗ U` has the
same depth). The reconstruction uses any eigenvector rule satisfying `IsTopEigRule`, and its output
is a unit vector for every histogram data. The expectation is over the independent levels' bases
and outcomes (`initExpect`). `O(log n)` is `≤ C(⌊log₂ n⌋ + 1)`. -/
theorem theorem_5_1 :
    ∃ K C : ℕ, ∀ [∀ k, Fintype (CliffordLabel k)] (n : ℕ),
      (∑ ℓ ∈ Finset.range n, ((initN K n * initS K n ℓ : ℕ) : ℝ)) ≤ C * 2 ^ n ∧
      (∑ _ℓ ∈ Finset.range n, ((initN K n : ℕ) : ℝ)) ≤ C * (n : ℝ) ^ 3 ∧
      (∃ circ : (j : ℕ) → SuffixLabel n j → Circuit j, ∀ j : ℕ, 1 ≤ j → j ≤ n →
        ∀ lab : SuffixLabel n j,
          Circuit.IsValid (circ j lab) ∧ (depth (circ j lab) : ℝ) ≤ C * (Nat.log 2 n + 1) ∧
          ∃ c : ℂ, ‖c‖ = 1 ∧ circUnitary (circ j lab) = c • (suffixEnsemble n j).mat lab) ∧
      ∀ choose : Matrix (Fin 2) (Fin 2) ℂ → Fin 2 → ℂ, IsTopEigRule choose →
        (∀ rec : (j : Fin n) → Fin (initN K n) →
            SuffixLabel n (j.1 + 1) × (Bits (n - (j.1 + 1)) × Bits (j.1 + 1) → ℕ),
          IsUnitVec (initOutput (fun j => suffixEnsemble n j) choose (fun _ => initN K n)
            (initS K n) rec)) ∧
        ∀ ψ : Bits n → ℂ, IsUnitVec ψ →
          11 / 12 ≤ initExpect (fun j => suffixEnsemble n j) choose (fun _ => initN K n)
            (initS K n) ψ (fun v => if 1 / 2 ≤ ‖braket ψ v‖ ^ 2 then 1 else 0) := by sorry

end ShadowBootstrap
