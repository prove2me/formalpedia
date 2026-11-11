-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_proposition_4_5
-- name    : UnitaryQIPPSPACE.proposition_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:27.678869+00:00
-- url     : https://prove2.me/theorems/9726c82c-10a8-40f6-ad8c-1d3422fd7f58
-- title:
--   Proposition 4.5 — the rounded unitary has PSPACE-computable entries
-- statement:
--   Let $\{U_n\}\in\mathsf{unitaryPSPACE}_\gamma$ with $\gamma:\mathbb N\to[0,2^{-10}]$, witnessed by a space-uniform circuit family $\{C_n\}$ with $\mathrm{TD}(C_n(\psi),U_n\psi U_n^\dagger)\le\gamma(n)$ for every unit $|\psi\rangle$ and every $n\ge n_0$. Then the top eigenvectors $|v_n\rangle$ of $\sigma_n=C_n(|0^n\rangle\langle0^n|)$, $n\ge n_0$, can be chosen so that the family
--   $$W_n=B_n(B_n^\dagger B_n)^{-1/2}\ (n\ge n_0),\qquad W_n=I\ (n<n_0),$$
--   with $B_n$ built by eq. (12) from $C_n$, $|0^n\rangle$ and $|v_n\rangle$, consists of unitaries with PSPACE-computable entries, and for every $n\ge n_0$ there is $|z_n|=1$ with
--   $$\|W_n-z_nU_n\|_{\mathrm{op}}\le16\sqrt{\gamma(n)}.$$
--
--   This makes a polynomial-space synthesizable family exactly synthesizable relative to a PSPACE oracle (Lemma 4.7).
--
--   Differences from the source:
--   - reading: "let W_n be the unitary obtained from Lemma 4.1" (the phase of |v_max⟩ unspecified) → there exists a choice of the unit top eigenvectors v_n for which the conclusion holds; reason: for an arbitrary choice the conclusion is false: with U_n = I, C_n the empty circuit (γ = 0) and v_n = (−1)^{[n∈K]}|0^n⟩ for an undecidable set K, W_n = (−1)^{[n∈K]}I has an uncomputable entry; the proof (pp. 23–24) fixes the canonical representative Π₁|j₀⟩/√⟨j₀|Π₁|j₀⟩
--   - encoding: the index (1^n, i, j) of an entry → tup [1^n, i, j] with i, j written as bit strings; reason: a fixed self-delimiting code, as the paper prescribes
--   - encoding: the gate set G is fixed "without loss of generality, … for example, {H, T, CNOT}" → G = {H, T, CNOT} exactly; reason: the paper's own example; the classes do not depend on the choice of a finite universal gate set
--   - encoding: deterministic Turing machines → the published oracle Turing machines QAdvFew.PoQOracle.OTM run with the empty oracle; descriptions are tuple codes; reason: a standard machine model and a fixed injective code; polynomial time and space are preserved
--   - reading: space-uniform: a polynomial-space machine "on input (1^n, i), outputs the i-th operation of C_n" → for every i ≤ |C_n| the machine on (1^n, bin i) uses at most p(n) cells and outputs the i-th operation, or the empty string at i = |C_n|; reason: the end marker makes the machine determine the circuit (the standard reading of [MY23]); it bounds |C_n| by 2^{O(p(n))}
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Proposition 4.5, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_unitaryPSPACEd
import Definitions.Def_UnitaryQIPPSPACE_roundB
import Definitions.Def_UnitaryQIPPSPACE_PSPACEComputableFam
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_AgnosticTNS_opNorm
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_UnitaryQIPPSPACE_conjBy

open Matrix

namespace UnitaryQIPPSPACE

/-- **Proposition 4.5 (PSPACE-computability of the rounded unitary)** (He, Ou, Zhao, *unitaryQIP =
unitaryPSPACE*, arXiv:2611.02819, held version sha256 9e357a00…, p. 23 (PDF p. 25)): "Let the unitary
family `{U_n} ∈ unitaryPSPACE_γ` with `γ : ℕ → [0, 2^{−10}]`, witnessed by a space-uniform circuit
family `{C_n}`. Suppose that there exists `n₀` such that, for every `n ≥ n₀` `TD(C_n(ψ), U_n(ψ)) ≤ γ`
for every `|ψ⟩`. For each `n ≥ n₀`, let `W_n` be the unitary obtained from Lemma 4.1 with `C = C_n`
and `|ϕ⟩ = |0^n⟩`, and set `W_n = I` for `n < n₀`. Then `{W_n}` is a family of unitaries with
PSPACE-computable entries, and for each `n ≥ n₀` there exists `z_n ∈ ℂ` with `|z_n| = 1` such that
`‖W_n − z_n U_n‖_op ≤ 16√γ(n)`."

The `W_n` of Lemma 4.1 is `B_n(B_n†B_n)^{−1/2}` with `B_n` built by eq. (12) from `C_n`, `|0^n⟩` and a
unit eigenvector `v_n` of `σ_n = C_n(|0^n⟩⟨0^n|)` for `λ_max(σ_n)`. The statement asserts that the
eigenvectors `v_n` (`n ≥ n₀`) can be chosen so that the resulting family has PSPACE-computable
entries.

**Formalization Note** Lemma 4.1 fixes `v_n` only up to a phase, and `W_n` scales with it. For an
arbitrary choice of phases the conclusion is false (with `U_n = I`, `C_n` empty and
`v_n = (−1)^{[n ∈ K]}|0^n⟩` for an undecidable set `K`, the entry `⟨0^n|W_n|0^n⟩ = (−1)^{[n∈K]}` is
not computable); the proof (pp. 23–24) fixes the canonical representative
`v = Π₁|j₀⟩/√⟨j₀|Π₁|j₀⟩`. Hence the existential reading. -/
theorem proposition_4_5 (U : UFam) (γ : ℕ → ℝ) (hγ : ∀ n, 0 ≤ γ n ∧ γ n ≤ (1 / 2 : ℝ) ^ 10)
    (C : ℕ → Circuit) (hSU : SpaceUniform C id) (hWF : ∀ n, (C n).WF n n) (n₀ : ℕ)
    (hTD : ∀ n ≥ n₀, ∀ ψ : Bits n → ℂ, ShadowBootstrap.IsUnitVec ψ →
      DimFreeShadow.traceDistance ((C n).chan n n (ObliviousRSP.pureState ψ)) (conjBy (U n : Matrix (Bits n) (Bits n) ℂ) (ObliviousRSP.pureState ψ))
        ≤ γ n) :
    ∃ v : (n : ℕ) → Bits n → ℂ,
      (∀ n ≥ n₀, ShadowBootstrap.IsUnitVec (v n) ∧
        ((C n).chan n n (ObliviousRSP.pureState (Pi.single (Bits.zero n) 1))).mulVec (v n) =
          ((SYKEdge.lamMax ((C n).chan n n (ObliviousRSP.pureState (Pi.single (Bits.zero n) 1))) : ℝ) : ℂ) • v n) ∧
      (∀ n, (if n₀ ≤ n then roundW (roundB ((C n).chan n n) (Pi.single (Bits.zero n) 1) (v n))
          else (1 : Matrix (Bits n) (Bits n) ℂ)) ∈ Matrix.unitaryGroup (Bits n) ℂ) ∧
      HasPSPACEEntries (fun n => if n₀ ≤ n then
        roundW (roundB ((C n).chan n n) (Pi.single (Bits.zero n) 1) (v n)) else 1) ∧
      ∀ n ≥ n₀, ∃ z : ℂ, ‖z‖ = 1 ∧
        AgnosticTNS.opNorm (roundW (roundB ((C n).chan n n) (Pi.single (Bits.zero n) 1) (v n))
          - z • (U n : Matrix (Bits n) (Bits n) ℂ)) ≤ 16 * Real.sqrt (γ n) := by sorry

end UnitaryQIPPSPACE
