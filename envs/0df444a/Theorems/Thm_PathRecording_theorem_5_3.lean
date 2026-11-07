-- Prove2me | Theorems.Thm_PathRecording_theorem_5_3
-- name    : PathRecording.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:10:45.196224+00:00
-- url     : https://prove2.me/theorems/fca4064d-fadb-4669-a5b9-b7d635993d79
-- title:
--   Theorem 5.3 — the path-recording oracle exactly simulates queries to $\rho(g)$ for Haar-random $g$
-- statement:
--   Let $G$ be a compact group with Haar probability measure $dg$, let $\rho:G\to U(N)$ be a continuous unitary representation on $V=\mathbb C^N$, and fix any Schur–Weyl data (Schur transforms) for every $\rho^{\otimes t}$. Let $\Gamma_t=(\mathrm{Schur}_t^\dagger\otimes\mathrm{Schur}_t^\top)E_t:\mathrm{Tab}_t\to\mathrm{Path}_t$ and let $F$ be the Fourier transform. Then for every $t\ge0$:
--
--   1. $\Gamma_t$ is a partial isometry: $\Gamma_t^\dagger\Gamma_t=I_{\mathrm{Tab}_t}$ and $\Gamma_t\Gamma_t^\dagger=\Omega_{\mathcal A_t}$;
--   2. on inputs in $V\otimes F^{-1}(\mathrm{Tab}_t)$,
--   $$Q^{\mathrm{Path}}_{\rho,t+1}\cdot(I_V\otimes\Gamma_t\cdot F)=(I_V\otimes\Gamma_{t+1}\cdot F)\cdot Q_\rho;\qquad(5.12)$$
--   3. for every $t$-query algorithm whose query register is $V$ (any finite workspace $B$, unitaries $A_1,\dots,A_t$, start state $\psi$), applying $I\otimes\Gamma_tF$ to the recording register of its final state against $Q_\rho$ (started from $\psi\otimes|1\rangle$) gives its final state against $Q^{\mathrm{Path}}_\rho$ (started from $\psi\otimes|\emptyset\rangle$): $A^{Q_\rho}(|\psi\rangle)\simeq A^{Q^{\mathrm{Path}}_\rho}(|\psi\rangle)$;
--   4. the two final states have the same reduced state on the algorithm's registers $A\otimes B$;
--   5. that reduced state equals the Haar average $\mathbb E_{g\sim dg}\,|A^{\rho(g)}\psi\rangle\langle A^{\rho(g)}\psi|$ of running the algorithm against the fixed unitary $\rho(g)$.
--
--   So an algorithm querying a Haar-random $\rho(g)$ cannot tell it apart from the stateful path-recording oracle.
--
--   Differences from the source:
--   - generalization: "there is a sequence of partial isometries Γ_t" → the explicit Γ_t = (Schur_t† ⊗ Schur_tᵀ)E_t of §5.3, with Γ_t†Γ_t = I_{Tab_t} and Γ_tΓ_t† = Ω_{𝒜_t} (Claim 5.4); reason: Γ_t = 0 satisfies the printed (5.12); the explicit isometric witness is the one the proof constructs and implies the existence claim
--   - encoding: the Peter–Weyl Fourier transform F on L²(G), Γ_t on all blocks λ ∈ Ĝ and the subspace F⁻¹(Tab_t) → Γ_t on Tab_t only, fourierTrunc (the coefficients ⟪F⁻¹|λ,X,Y⟩, f⟫ for λ ∈ Ĝ_t, i.e. F followed by the projection onto Tab_t) and matrixCoeffSpace (the span of F⁻¹|λ,X,Y⟩ = √d_λ⟨Y|ρ_λ(·)|X⟩, λ ∈ Ĝ_t); reason: F is unitary with F⁻¹|λ,X,Y⟩ given by Definition 3.7, and Γ_t vanishes off Tab_t, so Γ_t·F = Γ_t·fourierTrunc and F⁻¹(Tab_t) is that span; same instances
--   - reading: A^{Q_ρ}(|ψ⟩) ≃ A^{Q^{Path}_ρ}(|ψ⟩) via the fixed partial isometry Γ_t·F on the recording register → conjunct 3 (I ⊗ Γ_tF maps the uncompressed final state to the path final state) and conjunct 4 (equal reduced states on A ⊗ B); reason: ≃ via Γ_tF is stated as the map relation together with its consequence for the algorithm's view
--   - generalization: Theorem 5.3 (second claim) → conjunct 5: the reduced state also equals the Haar average of running the algorithm against ρ(g) (Theorem 1.5(3), p.12); reason: Theorem 1.5(3) is the informal form of Theorem 5.3; the extra conjunct is implied by the uncompressed oracle being the purification of a Haar-random g
--   - encoding: the generalized Schur transform Schur_t : V^{⊗t} → ⨁_λ V^λ_G ⊗ V^λ_{𝒜_t} (Definition 3.22, Theorem 3.11) → an arbitrary SchurWeylData ρ t: a finite label type (Ĝ_t), irreducible, pairwise non-isomorphic continuous unitary matrix irreps on ℂ^{dG λ}, multiplicity dimensions dA λ > 0, and a unitary matrix schur with schur ρ^{⊗t}(g) schur† = ⨁_λ ρ_λ(g) ⊗ I; reason: the paper's Schur transform is any such family; stating the result for every choice covers the paper's choice, and the operators depend on it only through its blocks
--   - generalization: G a compact Lie group with its normalized Haar measure dg → G any compact topological group with a Borel σ-algebra and a left Haar probability measure μ; reason: the Lie structure is never used; a compact Lie group is such a group, and on it (second countable) every left Haar probability measure is the normalized, regular, bi-invariant Haar measure of Definition 3.1; on a general compact group Lean also admits left Haar measures that are not regular, which only enlarges the statement
--   - generalization: a t-query algorithm whose query register is V, on n + m qubits started from |0⟩ (Definition 3.5) → query register V = ℂ^N, any finite workspace B, any unitaries, any start vector ψ (not necessarily a unit vector); reason: Theorem 5.3 says "for all input states |ψ⟩"; qubit registers and unit start vectors are special cases
--   - encoding: Path_t = V^{⊗t} ⊗ \overline{V}^{⊗t} and the double Schur transform Schur_t ⊗ \overline{Schur_t} → vectors indexed by pairs (x⃗, y⃗) of Fin t → Fin N, and the Kronecker product of schur with its entrywise conjugate (inverse Schur_t† ⊗ Schur_tᵀ); reason: a linear map on the conjugate space is the conjugate matrix in the conjugate basis; same instances
--   - encoding: V ⊗ L²(G) with Q_ρ(|x⟩⊗|f⟩) = ∫ f(g) ρ(g)|x⟩⊗|g⟩ dg → Fin N → Lp ℂ 2 μ, with (Q_ρ φ)_y = Σ_x ⟨y|ρ(·)|x⟩ · φ_x (multiplication by the continuous matrix entries as L^∞ functions); reason: (4.1) extended linearly; V ⊗ L²(G) ≅ L²(G)^N
--   - generalization: one Fourier transform F, with one fixed basis of each V_λ, on both sides of (5.12) → Γ_tF_t built from the irrep matrices of the data at t and Γ_{t+1}F_{t+1} from those of the data at t+1, which may use different bases or representatives; reason: the paper's fixed F is the case where the data at all t share their irrep matrices; the identity holds for every family
--   - encoding: the list (A_1,…,A_t), the database register started at |∅⟩, and tr_R (Definition 3.5, §4.1) → a sequence A : ℕ → U(Fin N × B) of which a t-query run reads the first t, B : Type finite, start ψ ⊗ |1⟩ against Q_ρ and ψ ⊗ |∅⟩ with Path_0 = ℂ against Q^{Path}, reduced states as explicit matrices (reducedUnc, reducedPath, haarAverage); reason: any list extends to a sequence; every finite workspace has an equivalent in Type; §4.1 initializes L²(G) to |1⟩; the matrices are the entries of tr_R |φ⟩⟨φ|
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Theorem 5.3, Eq. (5.12), p.63, with its proof pp.63–67 (Claim 5.4, p.64), and Theorem 1.5(3), p.12

import Mathlib
import Definitions.Def_PathRecording_adversary

set_option autoImplicit false

namespace PathRecording

open Matrix MeasureTheory
open scoped InnerProductSpace

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Theorem 5.3 (Correctness of the path-recording oracle), p.63, with Theorem 1.5(3),
p.12. Let `G` be a compact group with Haar probability measure `μ`, `ρ : G → U(N)` a continuous
unitary representation and `S` any family of Schur–Weyl data (Schur transforms) of the `ρ^{⊗t}`.
For every `t`, the explicit partial isometry `Γ_t = (Schur_t† ⊗ Schur_tᵀ) E_t` satisfies:
1. `Γ_t† Γ_t = I_{Tab_t}` and `Γ_t Γ_t† = Ω_{𝒜_t}` (Claim 5.4);
2. `Q^{Path}_{ρ,t+1} (I_V ⊗ Γ_t F) = (I_V ⊗ Γ_{t+1} F) Q_ρ` on `V ⊗ F⁻¹(Tab_t)` (5.12);
3. for every `t`-query algorithm (any finite workspace `B`, unitaries `A`, start state `ψ`),
   `(I ⊗ Γ_t F)` maps its final state against `Q_ρ` (from `ψ ⊗ |1⟩`) to its final state against
   `Q^{Path}_ρ` (from `ψ ⊗ |∅⟩`);
4. the two final states have the same reduced state on the algorithm's registers;
5. that reduced state is the Haar average `E_{g∼μ} |A^{ρ(g)}ψ⟩⟨A^{ρ(g)}ψ|`.

**Formalization Note.** `Γ_t F` is `gammaF μ (S t)` (`F` truncated to `Tab_t`, where `Γ_t` is
supported); `F⁻¹(Tab_t)` is `matrixCoeffSpace μ (S t)`. The run semantics and the reduced states
are those of the `adversary` definitions. -/
theorem theorem_5_3 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {N : ℕ} (ρ : UnitaryRep G N) (S : (t : ℕ) → SchurWeylData ρ t) (t : ℕ) :
    ((S t).Gammaᴴ * (S t).Gamma = 1 ∧ (S t).Gamma * (S t).Gammaᴴ = (S t).omega) ∧
    (∀ φ : Fin N → Lp ℂ 2 μ, (∀ x, φ x ∈ matrixCoeffSpace μ (S t)) →
      (fun q : Fin N × PathIdx N (t + 1) => gammaF μ (S (t + 1)) (oracle μ ρ φ q.1) q.2) =
        pathOracle (S t) (S (t + 1)) *ᵥ fun q : Fin N × PathIdx N t => gammaF μ (S t) (φ q.1) q.2) ∧
    (∀ (B : Type) [Fintype B] [DecidableEq B] (A : ℕ → Matrix.unitaryGroup (Fin N × B) ℂ)
        (ψ : Fin N × B → ℂ),
      (fun q : (Fin N × B) × PathIdx N t => gammaF μ (S t) (uncompressedRun μ B ρ A ψ t q.1) q.2) =
          pathRun B S A ψ t ∧
        reducedUnc μ B (uncompressedRun μ B ρ A ψ t) = reducedPath B (pathRun B S A ψ t) ∧
        haarAverage μ B ρ A ψ t = reducedPath B (pathRun B S A ψ t)) := by sorry

end PathRecording
