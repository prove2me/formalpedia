-- Prove2me | Theorems.Thm_ShadowBootstrap_lemma_6_3
-- name    : ShadowBootstrap.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:38.100065+00:00
-- url     : https://prove2.me/theorems/de198542-2a69-466a-80d9-a7cdafd91e46
-- title:
--   Lemma 6.3 — the shadow action $[\sum_z h_z\mathcal M^{-1}(U^\dagger|z\rangle\langle z|U)]x$ in $\tilde O(d)$ time and memory
-- statement:
--   Two parts.
--
--   **(a) The identity of the proof.** Let $E$ be a Clifford ensemble with invertible shadow channel $\mathcal M$ and $U$ a unitary of $E$ (positive weight). For every $h \in \mathbb C^d$,
--   $$\sum_z h_z\,\mathcal M^{-1}\big(U^\dagger|z\rangle\langle z|U\big) = U^\dagger\operatorname{diag}\big(\mathrm{WH}^{-1}(\mu)\big)U,\qquad \mu_a := m^{-1}_{U^\dagger Z_aU}\,\mathrm{WH}(h)_a .$$
--
--   **(b) The computation.** There is one real-RAM program with rational literals and no randomness such that, for every depth constant $D$, there is a constant $C$ with the following property. For every $n$, every suffix size $1 \le j \le n$, every unitary $U$ of the ensemble $E_{n-j}$ of Lemma A.2 given as a valid circuit over $\{H,S,CX\}$ of depth at most $D(\lfloor\log_2 n\rfloor + 1)$ (up to a global phase), and all $h, x \in \mathbb C^{2^j}$, the program, given $n$, $j$, the gate list, $h$ and $x$, halts within $C\,2^j(n+1)^C$ steps, writes at most $C\,2^j(n+1)^C$ cells, and outputs exactly
--   $$\Big[\sum_z h_z\,\mathcal M^{-1}\big(U^\dagger|z\rangle\langle z|U\big)\Big]x .$$
--
--   This is how both the initialization and the bootstrapping stages process each histogram without forming a $d\times d$ matrix.
--
--   Differences from the source:
--   - reading: can be computed in Õ(d) time and Õ(d) working memory → one real-RAM program (exact √, rational literals, no randomness; two-bank input, distinct cells written) halting within C·2^j(n+1)^C steps and writing ≤ C·2^j(n+1)^C cells, C depending only on the depth constant; reason: the paper counts arithmetic operations; Õ is polylogarithmic in the dimension and the lemma has no ϵ or δ
--   - generalization: our two-layer Clifford ensemble (k | n) → every suffix ensemble E_{n−j} of Lemma A.2, 1 ≤ j ≤ n (j = n is the bootstrapping ensemble); reason: §6.1 applies the same construction to the suffix channels M_ℓ
--   - generalization: (the proof's identity) → stated as conjunct (a) for every Clifford ensemble with invertible channel; reason: the derivation uses only Eq. (4) and the Clifford property
--   - encoding: a measurement circuit U, vectors h, x → a valid {H, S, CX} circuit realizing a unitary of the ensemble up to a global phase; h, x as real and imaginary parts in index order; reason: the paper's input
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma 6.3 and its proof, p.24; Algorithm 2, p.26; Lemmas 6.1–6.2, p.23

import Mathlib
import Definitions.Def_ShadowBootstrap_walshHadamard
import Definitions.Def_ShadowBootstrap_Schedule
import Definitions.Def_ShadowBootstrap_suffixEnsemble
import Definitions.Def_ShallowShadows_ShadowNorm_IsCliffordPrimitive

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma 6.3, p.24 (shadow action): let `M` be the shadow channel of the two-layer Clifford
ensemble. Given a measurement circuit `U` and vectors `h = (h_z)_z, x ∈ ℂ^d`, the vector
`[Σ_z h_z M⁻¹(U†|z⟩⟨z|U)] x` can be computed in `Õ(d)` time and `Õ(d)` working memory.

**Formalization Note** Two conjuncts. (a) The identity of the proof (p.24): for every unitary
`U` of a Clifford ensemble with invertible shadow channel and every `h ∈ ℂ^d`,
`Σ_z h_z M⁻¹(U†|z⟩⟨z|U) = U† diag(WH⁻¹(µ)) U` with `µ_a := m⁻¹_{U†Z_aU} WH(h)_a` (Walsh–Hadamard
transforms of §3.5, visibility of Eq. (4)). (b) The computation, for the ensembles of Lemma A.2 on
`j ≤ n` qubits (`j = n` is the ensemble of the bootstrapping stages, the suffixes are those of
§6.1): one real-RAM program, given `n`, `j`, the gate list of a valid `{H, S, CX}` circuit `c` of
depth `≤ D(⌊log₂ n⌋ + 1)` realizing a unitary of the ensemble up to a global phase (index cells), and
`h, x` as real and imaginary parts in index order (real cells), halts within `C·2^j(n+1)^C` steps,
writes at most `C·2^j(n+1)^C` cells and outputs the vector exactly; `C` depends only on `D`. `Õ`
is polylogarithmic in the dimension; the lemma has no `ϵ` or `δ`. -/
theorem lemma_6_3 :
    (∀ (n : ℕ) {ι : Type} [Fintype ι] (E : Primitive n ι), IsCliffordPrimitive E →
      IsUnit (measChannel E) → ∀ i : ι, 0 < E.w.prob i → ∀ h : Bits n → ℂ,
        ∑ z, h z • shadow E (i, z) =
          star (E.mat i) *
            Matrix.diagonal (walshHadamardInv fun a =>
              walshHadamard h a / ((vis E (star (E.mat i) * zString a * E.mat i) : ℝ) : ℂ)) *
            E.mat i) ∧
    ∃ P : MatMulTimeLP.Program, RationalLiterals P ∧ NoRandom P ∧
      ∀ D : ℝ, ∃ C : ℝ, ∀ [∀ k, Fintype (CliffordLabel k)] (n j : ℕ), 1 ≤ j → j ≤ n →
        ∀ (lab : SuffixLabel n j) (c : Circuit j), Circuit.IsValid c →
          (depth c : ℝ) ≤ D * (Nat.log 2 n + 1) →
          (∃ ph : ℂ, ‖ph‖ = 1 ∧ circUnitary c = ph • (suffixEnsemble n j).mat lab) →
          ∀ h x : Bits j → ℂ,
            HaltsWithin P (initState2 (complexList h ++ complexList x) (n :: j :: encodeCircuit c))
                (C * 2 ^ j * ((n : ℝ) + 1) ^ C) ∧
            (cellsWritten P (initState2 (complexList h ++ complexList x)
                (n :: j :: encodeCircuit c)) : ℝ) ≤ C * 2 ^ j * ((n : ℝ) + 1) ^ C ∧
            outputVec P (initState2 (complexList h ++ complexList x) (n :: j :: encodeCircuit c))
                (complexList h ++ complexList x).length j =
              (∑ z, h z • shadow (suffixEnsemble n j) (lab, z)).mulVec x := by sorry

end ShadowBootstrap
