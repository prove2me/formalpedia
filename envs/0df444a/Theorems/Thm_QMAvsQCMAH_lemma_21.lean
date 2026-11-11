-- Prove2me | Theorems.Thm_QMAvsQCMAH_lemma_21
-- name    : QMAvsQCMAH.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:09.171557+00:00
-- url     : https://prove2.me/theorems/dba1155d-70b0-40e6-8f22-c1e83b54cf61
-- title:
--   Lemma 21 — random access codes: $\Pr[M_i(\sigma_x)=x_i]\le\frac12+\sqrt{m/N}$
-- statement:
--   Let $x\mapsto\sigma_x$ encode $x\in\{0,1\}^N$ into $m$ qubits, and let $M_1,\dots,M_N$ be binary measurements, where $N\ge1$ and $m\ge0$ are integers. Then
--   $$\Pr_{x\leftarrow\{0,1\}^N,\ i\leftarrow[N]}[M_i(\sigma_x)=x_i]\le\frac12+\sqrt{\frac mN}.$$
--
--   This is Nayak's random-access-code bound in averaged form; it bounds the recovery probability in the proof of Lemma 12.
--
--   Differences from the source:
--   - encoding: binary measurements M_i → the outcome-1 element M_i with 0 ≤ M_i ≤ I; Pr[M_i(σ) = 1] = tr(M_i σ); reason: standard description of a two-outcome measurement
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 21, p.87 (PDF p.90)

import Definitions.Def_QMAvsQCMAH_Normalized

set_option autoImplicit false

namespace QMAvsQCMAH

open ComplexOrder

/-- **Lemma 21 (Random access codes).** Let `x ↦ σ_x` encode `x ∈ {0,1}^N` into `m` qubits, and
let `M_1, …, M_N` be binary measurements, where `N ≥ 1` and `m ≥ 0`. Then
`Pr_{x ← {0,1}^N, i ← [N]}[M_i(σ_x) = x_i] ≤ 1/2 + √(m/N)`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 21, p.87 (PDF p.90): "Let x ↦ σx encode x ∈ {0, 1}^N into m qubits, and let
M1, …, MN be binary measurements, where N ≥ 1 and m ≥ 0 are integers. Then
Pr_{x←{0,1}^N, i←[N]}[Mi(σx) = xi] ≤ 1/2 + √(m/N)."

**Formalization Note.** `σ_x` are density operators on `m` qubits; the binary measurement `M_i`
is its outcome-`1` element (`0 ≤ M_i ≤ I`), so `Pr[M_i(σ) = 1] = tr(M_i σ)`. The probability is
averaged over uniform `x` and uniform `i`; no per-index success hypothesis is assumed. -/
theorem lemma_21 (N m : ℕ) (hN : 1 ≤ N) (σ : (Fin N → Bool) → Matrix (Fin m → Bool) (Fin m → Bool) ℂ) (hσ : ∀ x, IsDensity (σ x)) (M : Fin N → Matrix (Fin m → Bool) (Fin m → Bool) ℂ) (hM : ∀ i, (M i).PosSemidef ∧ (1 - M i).PosSemidef) : ((2 : ℝ) ^ N)⁻¹ * (N : ℝ)⁻¹ * ∑ x : Fin N → Bool, ∑ i : Fin N, (if x i then ((M i * σ x).trace).re else (((1 - M i) * σ x).trace).re) ≤ 1 / 2 + Real.sqrt ((m : ℝ) / N) := by sorry

end QMAvsQCMAH
