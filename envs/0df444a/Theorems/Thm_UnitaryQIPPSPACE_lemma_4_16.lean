-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_lemma_4_16
-- name    : UnitaryQIPPSPACE.lemma_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:18.189211+00:00
-- url     : https://prove2.me/theorems/db083f85-c6e9-45a9-8289-bae595c9325d
-- title:
--   Lemma 4.16 — accepted map via verified phase states
-- statement:
--   Let $\Gamma(z,x)$ be a PSPACE predicate. There is a deterministic polynomial-time algorithm that, on input $(z,1^m,1^R)$ with $m,R\ge1$, outputs a well-formed quantum verifier of size $\mathrm{poly}(|z|+m+R)$ with no quantum input and an $m$-qubit output register $B$ such that
--   1. some honest prover makes the verifier accept with probability $1$;
--   2. for every prover, with its initial private state on $P$ regarded as an input and $\mathcal A:\mathcal L(\mathcal H_P)\to\mathcal L(\mathcal H_B\otimes\mathcal H_P)$ the unnormalized accepted map, there is a completely positive trace-non-increasing $\Lambda:\mathcal L(\mathcal H_P)\to\mathcal L(\mathcal H_P)$ with
--   $$D_\diamond\big(\mathcal A,\ |\varphi_{\Gamma_{z,m}}\rangle\langle\varphi_{\Gamma_{z,m}}|\otimes\Lambda\big)\le\frac1R,$$
--   where $\Gamma_{z,m}(x)=\Gamma(z,x)$.
--
--   This is the interactive preparation of the resource states, with the prover's leftover memory separated out.
--
--   Differences from the source:
--   - encoding: a PSPACE predicate Γ(z, x) → a language Γ ∈ PSPACE read on tup [z, x]; reason: a fixed pair code
--   - encoding: poly(|z| + m + R) size, polynomial time → one polynomial p bounding both the running time and the size; reason: equivalent
--   - encoding: the gate set G is fixed "without loss of generality, … for example, {H, T, CNOT}" → G = {H, T, CNOT} exactly; reason: the paper's own example; the classes do not depend on the choice of a finite universal gate set
--   - encoding: deterministic Turing machines → the published oracle Turing machines QAdvFew.PoQOracle.OTM run with the empty oracle; descriptions are tuple codes; reason: a standard machine model and a fixed injective code; polynomial time and space are preserved
--   - encoding: a prover is a unitary on (M, Y) with an arbitrarily large private register Y → any number y of private qubits and any unitary on M ⊗ Y, private register starting in |0⋯0⟩; reason: the paper's model, with y chosen by the prover
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 4.16, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_run
import Definitions.Def_UnitaryQIPPSPACE_SpaceUniform
import Definitions.Def_UnitaryQIPPSPACE_IsCP
import Definitions.Def_UnitaryQIPPSPACE_diamondDist
import Definitions.Def_UnitaryQIPPSPACE_predPhaseState
import Definitions.Def_ObliviousRSP_pureState

open Matrix QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- **Lemma 4.16 (Accepted map via verified phase states)** (He, Ou, Zhao, *unitaryQIP =
unitaryPSPACE*, arXiv:2611.02819, held version sha256 9e357a00…, p. 31 (PDF p. 33)): "Let `Γ(z, x)`
be a PSPACE predicate. There exists a deterministic polynomial-time algorithm that, on input
`(z, 1^m, 1^R)` with `z ∈ {0,1}*` and integers `m, R ≥ 1`, outputs a `poly(|z| + m + R)`-size quantum
verifier with no quantum input and an `m`-qubit output register `B`, such that
1. There exists an honest prover such that the verifier accepts with probability 1.
2. For every fixed prover, regard its initial private state on `P` as an input, and let
`A : L(H_P) → L(H_B ⊗ H_P)` be the unnormalized accepted map. Then there exists a completely positive
and trace-nonincreasing map `Λ : L(H_P) → L(H_P)` such that `D⋄(A, |φ_{Γ_{z,m}}⟩⟨φ_{Γ_{z,m}}| ⊗ Λ) ≤ 1/R`,
where `Γ_{z,m} : {0,1}^m → {0,1}` is defined by `Γ_{z,m}(x) = Γ(z, x)`, and `|φ_{Γ_{z,m}}⟩` is its
associated phase state as defined in Definition 4.9.
Notably, with `Γ` fixed, the verifier is generated uniformly from `(z, 1^m, 1^R)`."

The predicate `Γ` is a language in `PSPACE` read on `tup [z, x]`. The algorithm is a machine `M`
with polynomial `p`: on `tup [z, 1^m, 1^R]` it has halted after `p(|z| + m + R)` steps with the
description of the verifier `G(z, m, R)`, whose size is at most `p(|z| + m + R)`, which is well
formed, and whose output register `Z_out = B` has `m` qubits. "No quantum input": the input has `0`
qubits. Clause 1: some prover (private register starting in `|0⋯0⟩`) is accepted with probability
`1`. Clause 2: for every prover (`y` private qubits, unitary on `M ⊗ P`), the accepted map
`A(σ) = tr_{Z∖Z_out, M}(|1⟩⟨1|_{flag} ρ_{2k}(σ))`, `σ` the initial state of `P`, is within diamond
distance `1/R` of `σ ↦ |φ_{Γ_{z,m}}⟩⟨φ_{Γ_{z,m}}| ⊗ Λ(σ)` for some CP trace-non-increasing linear `Λ`.

**Formalization Note** Machines are the published `QAdvFew.PoQOracle.OTM` with the empty oracle;
`PSPACE` is `QAdvFew.PoQOracle.PSPACE` with the empty oracle. -/
theorem lemma_4_16 (Γ : Set Str) (hΓ : Γ ∈ PSPACE noOracle) :
    ∃ (G : Str → ℕ → ℕ → Verifier) (M : OTM) (p : Polynomial ℕ),
      ∀ (z : Str) (m R : ℕ), 1 ≤ m → 1 ≤ R →
        M.result noOracle (tup [z, unary m, unary R]) (p.eval (z.length + m + R)) ≠ none ∧
        M.output noOracle (tup [z, unary m, unary R]) (p.eval (z.length + m + R)) = (G z m R).code ∧
        (G z m R).size ≤ p.eval (z.length + m + R) ∧ (G z m R).WF ∧ (G z m R).o = m ∧
        (∃ P : Prover (G z m R).m,
          acceptProb (G z m R) (P.U : Matrix _ _ ℂ) 0 (fun _ => 1) (zeroState P.y) = 1) ∧
        ∀ P : Prover (G z m R).m,
          ∃ Λ : Matrix (Bits P.y) (Bits P.y) ℂ →ₗ[ℂ] Matrix (Bits P.y) (Bits P.y) ℂ,
            IsCP Λ ∧ IsTNI Λ ∧
            diamondDist (acceptedMap (G z m R) (P.U : Matrix _ _ ℂ) 0 (fun _ => 1))
              (fun σ => Matrix.kronecker (ObliviousRSP.pureState (predPhaseState Γ z (G z m R).o)) (Λ σ))
              ≤ 1 / (R : ℝ) := by sorry

end UnitaryQIPPSPACE
