-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_74
-- name    : SingleInteraction.Supplement.theorem_74
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:13:37.2622+00:00
-- url     : https://prove2.me/theorems/cdce84d8-45bf-43f1-8e91-81442a31a397
-- title:
--   Theorem 74 — stoquastic embedding: $p$-Pinned SIH$_k$ (real pinned state) $\to$ $(p+1)$-Pinned Stoq-SIH$_{k+2}$ with $S(h)$, spectrum doubled
-- statement:
--   Fix $k$ and $p$ ($p=0$ is the unpinned case). For a $k$-qubit Hermitian interaction $h$, the interaction $S(h)=R(h)^-\otimes I_c-R(h)^+\otimes X_c$ with $R(h)=\Phi(h)$ (eq. (57)) is Hermitian and stoquastic on $k+2$ qubits, with polynomial-time computable entries when $h$ has them. There is a polynomial-time reduction that maps every $p$-Pinned SIH$_k$ instance whose pinned state $|\psi_{\mathrm{pin}}\rangle$ has real amplitudes in the computational basis to a $(p+1)$-Pinned Stoq-SIH$_{k+2}$ instance with interaction $S(h)$ such that
--
--   1. the output has two new qubits and the same thresholds;
--   2. the original pinned register stays pinned to $|\psi_{\mathrm{pin}}\rangle$, the new sign qubit is pinned to $|-\rangle$, and the realification qubit stays unpinned;
--   3. the restricted spectrum of the output Hamiltonian is exactly the spectrum of the original pinned Hamiltonian $H_{\mathrm{pin}}$ with every eigenvalue appearing twice; in particular YES instances go to YES instances and NO instances to NO instances.
--
--   The same holds for DSIH$_k$: for a uniform Hermitian family $\{h^{(n)}\}$ the family $\hat h^{(n')}=S(h^{(n'-2)})$ ($n'\ge3$) is uniform, Hermitian and stoquastic, and the same reduction maps $p$-Pinned DSIH$_k$ to $(p+1)$-Pinned Stoq-DSIH$_{k+2}$ with the doubled spectrum.
--
--   Stoquasticity of the interaction therefore costs nothing in complexity once one qubit may be pinned.
--
--   Differences from the source:
--   - encoding: p = 0 denotes the unpinned case → the pinned problem with an empty pinned register (promise on λmin of H); reason: with p = 0 the compression is H itself and the λmin promise equals the energy promise of SIH_k
--   - encoding: there is a polynomial-time reduction; the restricted spectrum … with every eigenvalue appearing twice → one map f, TM2ComputableInPolyTime on the pinned-instance codes, with: output valid at some exponent c′, n + 2 qubits, same thresholds, pins = old pins ++ [new qubit], pinned state |ψpin⟩ ⊗ |−⟩, multiplicity of every real μ doubled, YES ↦ YES and NO ↦ NO; reason: these are the properties the theorem and its proof (pp.86–87) assert
--   - reading: a (p + 1)-Pinned Stoq-SIH_{k+2} instance → the instance for the interaction S(h) of eq. (57), shown Hermitian, stoquastic and with polynomial-time entries when h has them; reason: eq. (57) is the interaction the theorem refers to (p.85)
--   - encoding: the same statement holds for DSIH_k → the DSIH clauses for instances with n ≥ 1, output family ĥ(n′) = S(h(n′−2)) for n′ ≥ 3 and 0 otherwise; reason: the family is indexed by n ≥ 1 (Definition 32); the output family is the one of p.87
--   - encoding: pinned circuit over a fixed finite gate set, polynomial size (Definition 35) → a gate list over {H, T, CNOT} with at most (n+1)^c gates; the output adds gates preparing |−⟩ on the sign qubit; reason: the base gate set and the instance exponent
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 74, p.85

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_sihHam
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_UniformFamily
import Definitions.Def_SingleInteraction_Supplement_Linalg
import Definitions.Def_SingleInteraction_Supplement_Interactions
import Definitions.Def_SingleInteraction_Supplement_Pinned
import Definitions.Def_SingleInteraction_Supplement_Embedding

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-- Theorem 74 (Stoquastic embedding of a single-interaction problem) (Hecker, *The Complexity of
Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §7.2, p.85).

Fix `k` and `p` (`p = 0` is the unpinned case). For a `k`-qubit Hermitian `h`, the interaction
`S(h) = R(h)⁻ ⊗ I_c − R(h)⁺ ⊗ X_c`, `R(h) = Φ(h)` (eq. (57)), on `k + 2` qubits is Hermitian and
stoquastic, and has polynomial-time computable entries when `h` does; for a uniform family `{h^(n)}` of
Hermitian `k`-qubit matrices the family `ĥ(n′) = S(h^(n′−2))` (`n′ ≥ 3`, else `0`) is uniform, Hermitian
and stoquastic. There is one polynomial-time instance map `f` such that, for every exponent `c`, some
exponent `c′` has: for every valid `p`-pinned `k`-local instance `x` whose pinned state `|ψpin⟩` has real
amplitudes,
1. `f x` is a valid `(p+1)`-pinned `(k+2)`-local instance on `n + 2` qubits with the same thresholds;
2. its pinned register is the original one followed by one new qubit (the sign qubit), its pinned state
   is `|ψpin⟩ ⊗ |−⟩`, and the other new qubit (the realification qubit) is unpinned;
3. for every Hermitian `h`, every real `μ` has multiplicity in the compressed output Hamiltonian (with
   interaction `S(h)`) twice its multiplicity in the compressed input Hamiltonian `Hpin`; the same holds
   for every Hermitian family with `ĥ` when `n ≥ 1`;
4. consequently `f` maps YES to YES and NO to NO instances of `p`-Pinned `SIH_k` (resp. `DSIH_k`, for
   `n ≥ 1`) to `(p+1)`-Pinned Stoq-`SIH_{k+2}` with `S(h)` (resp. Stoq-`DSIH_{k+2}` with `ĥ`).

**Formalization Note** Pinned problems are `pinnedSihProblem` / `pinnedDsihProblem` (Definitions 35–38;
pinned circuits over `{H, T, CNOT}`); `p = 0` gives the unpinned problems in their `λmin` form.
Multiplicities are characteristic-polynomial root multiplicities (`eigMult`), so "every eigenvalue
appearing twice" includes "no other eigenvalues". The qubit order of `S(h)` is `(v1, …, vk, b, c)`.
The `DSIH` clauses assume `n ≥ 1` because the family is indexed by `n ≥ 1` (Definition 32). -/
theorem theorem_74 (k p : ℕ) :
    (∀ h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ, h.IsHermitian →
      (stoqEmbed h).IsHermitian ∧ IsStoquastic (stoqEmbed h) ∧
        (EntriesPolyTime h → EntriesPolyTime (stoqEmbed h))) ∧
    (∀ hfam : ℕ → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ,
      (∀ n : ℕ, 1 ≤ n → (hfam n).IsHermitian) → UniformFamily hfam →
        UniformFamily (stoqLiftFam hfam) ∧
          ∀ n : ℕ, 1 ≤ n → (stoqLiftFam hfam n).IsHermitian ∧ IsStoquastic (stoqLiftFam hfam n)) ∧
    ∃ f : PinnedInstance → PinnedInstance,
      Nonempty (Turing.TM2ComputableInPolyTime pinnedCodec.encode pinnedCodec.encode f) ∧
      ∀ c : ℕ, ∃ c' : ℕ, ∀ x : PinnedInstance, x.Valid k p c → RealPinned p x →
        (f x).Valid (k + 2) (p + 1) c' ∧ (f x).base.n = x.base.n + 2 ∧
        (f x).base.a = x.base.a ∧ (f x).base.b = x.base.b ∧
        (∃ s : ℕ, x.base.n ≤ s ∧ s < x.base.n + 2 ∧ (f x).pins = x.pins ++ [s]) ∧
        (∀ t : Fin (p + 1) → Fin 2, pinState (p + 1) (f x).gates t =
          pinState p x.gates (fun j => t (Fin.castSucc j)) * minusAmp (t (Fin.last p))) ∧
        (∀ h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ, h.IsHermitian →
          (∀ μ : ℝ, eigMult ((f x).compress (p + 1) (sihHam (k + 2) (stoqEmbed h) (f x).base)) μ =
            2 * eigMult (x.compress p (sihHam k h x.base)) μ) ∧
          (x ∈ (pinnedSihProblem k p h c).yes →
            f x ∈ (pinnedSihProblem (k + 2) (p + 1) (stoqEmbed h) c').yes) ∧
          (x ∈ (pinnedSihProblem k p h c).no →
            f x ∈ (pinnedSihProblem (k + 2) (p + 1) (stoqEmbed h) c').no)) ∧
        (∀ hfam : ℕ → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ,
          (∀ n : ℕ, 1 ≤ n → (hfam n).IsHermitian) → 1 ≤ x.base.n →
          (∀ μ : ℝ, eigMult ((f x).compress (p + 1)
              (sihHam (k + 2) (stoqLiftFam hfam (f x).base.n) (f x).base)) μ =
            2 * eigMult (x.compress p (sihHam k (hfam x.base.n) x.base)) μ) ∧
          (x ∈ (pinnedDsihProblem k p hfam c).yes →
            f x ∈ (pinnedDsihProblem (k + 2) (p + 1) (stoqLiftFam hfam) c').yes) ∧
          (x ∈ (pinnedDsihProblem k p hfam c).no →
            f x ∈ (pinnedDsihProblem (k + 2) (p + 1) (stoqLiftFam hfam) c').no)) := by sorry

end Supplement

end SingleInteraction
