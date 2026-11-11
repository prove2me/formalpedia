-- Prove2me | Theorems.Thm_PelagicFF_quantum_amplitudes
-- name    : PelagicFF.quantum_amplitudes
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:47.934781+00:00
-- url     : https://prove2.me/theorems/ee30f2b5-fc85-4c2f-9cb9-a8ec79df9c51
-- title:
--   §4.1, p.27 — $H^{\otimes n}U_g|\psi_f\rangle=\sum_y\widehat h(y)|y\rangle$
-- statement:
--   Let $f,g:\{0,1\}^n\to\{-1,1\}$, $h=fg$ and $N=2^n$. Applying the diagonal unitary $U_g$ and then $H^{\otimes n}$ to the phase state $|\psi_f\rangle=N^{-1/2}\sum_xf(x)|x\rangle$ gives
--   $$H^{\otimes n}U_g|\psi_f\rangle=\frac1N\sum_{y}\sum_{x}f(x)g(x)(-1)^{x\cdot y}|y\rangle=\sum_{y\in\{0,1\}^n}\widehat h(y)\,|y\rangle .$$
--
--   So Bob's measurement in the computational basis outputs $y$ with probability $|\widehat h(y)|^2$; with the mass bound of §4.1 this is the $n$-qubit protocol of Theorem 4.2.
--
--   **Formalization Note** The identity is stated coordinatewise, for the amplitude of each basis vector $|y\rangle$, as a complex number.
--
--   Differences from the source:
--   - encoding: Boolean functions with values in {−1,1} → Bool-valued functions read through OAI.Cotype.sign (false ↦ 1, true ↦ −1); reason: a bijection of value sets; same instances
--   - encoding: states and operators in Dirac notation → amplitude vectors (Fin n → Bool) → ℂ and matrices; H^{⊗n} by its entries 2^{−n/2}(−1)^{x·y}; reason: the computational-basis representation; same vectors
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §4.1, p.27

import Mathlib
import Definitions.Def_PelagicFF_PFF
import Definitions.Def_PelagicFF_hadamardN

open OAI.Cotype

namespace PelagicFF

/-- **Bob's output amplitudes (§4.1, p.27).** Applying `U_g` and then `H^{⊗n}` to the phase state
`|ψ_f⟩` gives `∑_y ĥ(y)|y⟩` with `h = f·g`: the amplitude of `|y⟩` is the Fourier coefficient
`ĥ(y)`.

arXiv:2610.05585 (held version, sha256 4564aef3…), §4.1, p.27: "|ψ_f⟩ = (1/√N) ∑ₓ f(x)|x⟩ ↦(U_g)
(1/√N) ∑ₓ f(x)g(x)|x⟩ ↦(H^{⊗n}) (1/N) ∑_y ∑ₓ f(x)g(x)(−1)^{x·y}|y⟩ = ∑_y ĥ(y)|y⟩".

**Formalization Note.** States are amplitude vectors indexed by `Fin n → Bool`; `Matrix.mulVec` is the
matrix–vector product. -/
theorem quantum_amplitudes (n : ℕ) (f g : BoolFn n) (y : Fin n → Bool) :
    (hadamardN n).mulVec ((signDiag g).mulVec (phaseState f)) y =
      ((OAI.Cotype.fourier (fun x => sign (f x) * sign (g x)) y : ℝ) : ℂ) := by sorry

end PelagicFF
