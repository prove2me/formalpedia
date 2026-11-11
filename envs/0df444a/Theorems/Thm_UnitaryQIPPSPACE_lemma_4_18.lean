-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_lemma_4_18
-- name    : UnitaryQIPPSPACE.lemma_4_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:01.812201+00:00
-- url     : https://prove2.me/theorems/4d65b1fb-a957-43be-b476-d7d19022df6f
-- title:
--   Lemma 4.18 — soundness of the composed protocol
-- statement:
--   Fix $n$ and a prover with initial private register $P$. Let $F$ be the accepted map of Protocol 4.17 and $\Phi_n(\rho)=\operatorname{tr}_E[C^{A}(\rho\otimes|0\rangle\langle0|_E)(C^{A})^\dagger]$. For every state $\sigma$ on $P$ there is a constant $\zeta(\sigma)\in[0,1]$, independent of the input, such that
--   $$D_\diamond(F_\sigma,\zeta(\sigma)\Phi_n)\le\frac KR,\qquad F_\sigma(\cdot)=F((\cdot)\otimes\sigma),$$
--   with $K=\sum_i(\ell_i+1)$ the number of resource states.
--
--   Stated here for every well-formed unitary oracle circuit $C$ on $n$ data qubits (as the circuit of Corollary 4.8 is), every language $A$, every subprotocol generator $G$ satisfying clause 2 of Lemma 4.16 for $\Gamma_A$ at parameter $R\ge1$, and every prover strategy.
--
--   The accepted map of the protocol is, up to the scalar $\zeta(\sigma)$, the channel of the oracle circuit, which gives soundness in Theorem 1.2.
--
--   Differences from the source:
--   - generalization: the circuit C_{n,β(n)} of Corollary 4.8, the oracle A_W, the verifier generator of Lemma 4.16 for Γ_{A_W}, R_n = ⌈8K q(n) r(n)⌉, a prover → any well-formed unitary oracle circuit on n data qubits (Corollary 4.8's circuit is well formed), any language A, any generator satisfying Lemma 4.16 clause 2 for Γ_A at R, any R ≥ 1, any prover strategy (a unitary per stage, chosen from the full history); reason: the printed objects are instances (Lemma 4.16 supplies such a generator; a prover of the paper is such a strategy); when K = 0 no subprotocol runs and the parameter is irrelevant
--   - encoding: K = ∑ᵢ (ℓᵢ + 1) → the total number of qubits named by the queries of C; reason: the same number
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 4.18, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_UnitaryQIPPSPACE_Protocol417_F
import Definitions.Def_UnitaryQIPPSPACE_IsCP
import Definitions.Def_UnitaryQIPPSPACE_diamondDist
import Definitions.Def_UnitaryQIPPSPACE_predPhaseState
import Definitions.Def_UnitaryQIPPSPACE_GammaLang
import Definitions.Def_ObliviousRSP_pureState

open Matrix QAlgorithms.Complexity
open scoped ComplexOrder

namespace UnitaryQIPPSPACE

/-- **Lemma 4.18 (Soundness of the composed protocol)** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, p. 35 (PDF p. 37)): "Fix `n` and a prover `P_n` with
initial private register `P`. Let `F` be the accepted map of Protocol 4.17, and let `Φ_n` be the
channel on `Q` defined by `Φ_n(ρ) := tr_E[C^{A_W}_{n,β(n)} (ρ ⊗ |0⟩⟨0|_E) (C^{A_W}_{n,β(n)})†]`. For every
state `σ ∈ L(H_P)`, there exists a constant `ζ(σ) ∈ [0, 1]` independent of `|ψ⟩` such that
`D⋄(F_σ, ζ(σ) · Φ_n) ≤ K/R_n`, where `F_σ(·) := F((·) ⊗ σ) : L(H_Q) → L(H_Q)`."

Stated for every instance of the protocol's ingredients (reading R15): every well-formed unitary
oracle circuit `C` (with `n` data qubits `Q` and ancillas `E`; every qubit it names exists, the
two qubits of a `CNOT` differ, and a query names distinct qubits), every language `A`, every subprotocol generator `G`
satisfying clause 2 of Lemma 4.16 for the predicate `Γ_A` of Lemma 4.13 at parameter `R` (and
producing `m`-qubit output registers), every `R ≥ 1`, every prover strategy (private register of
`y` qubits, a unitary per stage), and every density operator `σ` on `P`. `K` is the total number
`∑_i (ℓ_i + 1)` of qubits acted on by the queries of `C`.

**Formalization Note** The protocol uses `C = C_{n,β(n)}` of Corollary 4.8, `A = A_W`, the generator of
Lemma 4.16 for `Γ_{A_W}` and `R = R_n = ⌈8K q(n)r(n)⌉`; these are instances (when `K = 0` no
subprotocol runs and the parameter is irrelevant). The circuit of Corollary 4.8 is well formed
(`(Cg n β).Valid n` there); without well-formedness the lemma fails (a query naming the same
qubit twice acts by a non-unitary map in `Φ_n` but by a phase gate in the protocol). -/
theorem lemma_4_18 (n : ℕ) (C : OCirc) (A : Set Str) (G : Str → ℕ → ℕ → Verifier) (R : ℕ)
    (hC : C.Valid n) (hR : 1 ≤ R)
    (hG : ∀ (z : Str) (m : ℕ), 1 ≤ m → (G z m R).o = m ∧
      ∀ P : Prover (G z m R).m,
        ∃ Λ : Matrix (Bits P.y) (Bits P.y) ℂ →ₗ[ℂ] Matrix (Bits P.y) (Bits P.y) ℂ,
          IsCP Λ ∧ IsTNI Λ ∧
          diamondDist (acceptedMap (G z m R) (P.U : Matrix _ _ ℂ) 0 (fun _ => 1))
            (fun σ => Matrix.kronecker (ObliviousRSP.pureState (predPhaseState (GammaLang A) z (G z m R).o)) (Λ σ))
            ≤ 1 / (R : ℝ))
    (y : ℕ) (S : List Str → (mm : ℕ) → Matrix (Bits mm × Bits y) (Bits mm × Bits y) ℂ)
    (hS : ∀ h mm, S h mm ∈ Matrix.unitaryGroup (Bits mm × Bits y) ℂ)
    (σ : Matrix (Bits y) (Bits y) ℂ) (hσ : σ.PosSemidef) (hσ1 : σ.trace = 1) :
    ∃ ζ : ℝ, 0 ≤ ζ ∧ ζ ≤ 1 ∧
      diamondDist (Protocol417.F n C G R y S σ)
        (fun ρ => (ζ : ℂ) • oracleChannel (langOracle A) C n ρ)
        ≤ (C.queryWeight : ℝ) / (R : ℝ) := by sorry

end UnitaryQIPPSPACE
