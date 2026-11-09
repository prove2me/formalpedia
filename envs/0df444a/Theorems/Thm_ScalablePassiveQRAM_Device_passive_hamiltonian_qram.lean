-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_passive_hamiltonian_qram
-- name    : ScalablePassiveQRAM.Device.passive_hamiltonian_qram
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:32.673754+00:00
-- url     : https://prove2.me/theorems/87d3fdfa-965b-4b64-8504-9329d528a579
-- title:
--   Theorem 1 — Passive Hamiltonian QRAM
-- statement:
--   For $n\ge1$, the explicit physical Hamiltonian has no database parameter. It acts on $51\,2^n-18n-36$ qubits, its interaction terms are supported on at most four qubits, every qubit belongs to at most four terms, and there are at most $204\,2^n$ terms. Its schedule has $L=2n^2+4n+3$ steps.
--
--   $$e^{-iH\pi/\Omega}V_{\rm in}=e^{-i\pi L/2}V_{\rm out}U,\qquad \pi/\Omega\le\frac{9\pi n^2}{\Omega L}.$$
--
--   These are operator identities on arbitrary logical and memory superpositions with one global phase. In particular $\Omega=1/L$ gives runtime at most $9\pi n^2$. The term bound $204\,2^n$ follows from the degree bound and the qubit count in the source's proof.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
--   - generalization: couplings scaled as Ω=Θ(1/L) for the runtime statement → exact transfer at π/Ω for every Ω>0 with runtime bound 9πn²/(ΩL); reason: rescaling the stated Hamiltonian rescales time; Ω=1/L recovers the source runtime and no source instance is lost
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Theorem 1, p. 7. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance passive_hamiltonian_qramDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance passive_hamiltonian_qramDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem passive_hamiltonian_qram (n : ℕ) (hn : 1 ≤ n) (Ω : ℝ) (hΩ : 0 < Ω) :
    length n = 2*n^2+4*n+3 ∧
    Fintype.card (Qubit n) + 18*n + 36 = 51*2^n ∧
    (∀ j, j < length n → ∀ t ∈ transitions n j, t.support.card ≤ 4 ∧
      supportedOn n (t.support.image Sum.inr)
        (fun i j => if i.1 = j.1 then fullMatrix n t.operator i.2 j.2 else 0)) ∧
    (∀ q : Qubit n, ((List.range (length n)).map fun j =>
      ((transitions n j).filter fun t => decide (q ∈ t.support)).length).sum ≤ 4) ∧
    ((List.range (length n)).map fun j => (transitions n j).length).sum ≤ 204*2^n ∧
    evolve (hamiltonian n Ω) (Real.pi / Ω) * endpointEmbedding n 0 =
      Complex.exp (Complex.I * (phase (length n) : ℂ)) •
        (endpointEmbedding n (length n) * queryUnitary n) ∧
    Real.pi / Ω ≤ 9*Real.pi*(n:ℝ)^2 / (Ω * length n) := by sorry

end ScalablePassiveQRAM.Device
