-- Prove2me | Theorems.Thm_SpedalieriQHT_eq_21
-- name    : SpedalieriQHT.eq_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:56.39781+00:00
-- url     : https://prove2.me/theorems/709f6a70-7e8e-49f7-9767-c2a28efa15a5
-- title:
--   Eq. (21) — for two pure states, $C_s=|\langle\psi_0|\psi_1\rangle|^2=F$ on $0<s<1$
-- statement:
--   Let $\psi_0,\psi_1$ be unit vectors of a complex Hilbert space, $\rho_0=|\psi_0\rangle\langle\psi_0|$, $\rho_1=|\psi_1\rangle\langle\psi_1|$, and $0<s<1$. Then
--   $$
--   C_s=\operatorname{Tr}\bigl(\rho_0^{\,s}\rho_1^{\,1-s}\bigr)=\operatorname{Tr}\bigl(|\psi_0\rangle\langle\psi_0|\psi_1\rangle\langle\psi_1|\bigr)=|\langle\psi_0|\psi_1\rangle|^2=F(|\psi_0\rangle,|\psi_1\rangle).
--   $$
--
--   So for two pure states the s-overlap does not depend on $s\in(0,1)$, and $\ln C_s$ may be replaced by $\ln F$ in the quantum Hoeffding bound. The range is sharp: at $s=0$, $C_0=\operatorname{Tr}\rho_1=1$.
--
--   **Formalization Note** The four expressions are stated as a chain of three equalities; $\operatorname{Tr}(|\psi_0\rangle\langle\psi_0|\psi_1\rangle\langle\psi_1|)$ is the trace of the operator product $\rho_0\rho_1$.
--
--   Differences from the source:
--   - reading: $F(|\psi_0\rangle,|\psi_1\rangle)$ → $\langle\psi_0|\rho_1|\psi_0\rangle$ with $\rho_1=|\psi_1\rangle\langle\psi_1|$; reason: the paper's squared fidelity of a pure state and a state, whose value the equation itself gives as $|\langle\psi_0|\psi_1\rangle|^2$
--   - encoding: $|\psi\rangle\langle\psi|^s$, $\operatorname{Tr}$ → `CFC.rpow` powers of `rankOne ℂ ψ ψ` with $\|\psi\|=1$, basis-sum trace on an arbitrary complex Hilbert space, with $C_s$ its real part and the middle equality stated in $\mathbb C$; reason: Lean conventions; same instances
-- source:
--   Spedalieri–Braunstein, Asymmetric quantum hypothesis testing with Gaussian states, arXiv:1407.0884v3, Sec. III, Eq. (21), p.3

import Mathlib
import Definitions.Def_SpedalieriQHT_pureState
import Definitions.Def_SpedalieriQHT_pureFidelity
import Definitions.Def_SpedalieriQHT_sOverlap
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

open QAlgorithms.Papers.Independent.Next46.P02

namespace SpedalieriQHT

/-- **Eq. (21).** For unit vectors `ψ0, ψ1` and every `0 < s < 1`, the s-overlap of the pure
states `ρ0 = |ψ0⟩⟨ψ0|`, `ρ1 = |ψ1⟩⟨ψ1|` is `C_s = Tr(ρ0 ρ1) = |⟨ψ0|ψ1⟩|²`, and this is also
the fidelity `F(|ψ0⟩, |ψ1⟩) = ⟨ψ0|ρ1|ψ0⟩`.

Spedalieri–Braunstein, arXiv:1407.0884v3, Sec. III, Eq. (21), p.3: "for pure states
ρ0 = |ψ0⟩⟨ψ0| and ρ1 = |ψ1⟩⟨ψ1|, and for any 0 < s < 1, we can write
C_s = Tr(|ψ0⟩⟨ψ0|^s |ψ1⟩⟨ψ1|^{1−s}) = Tr(|ψ0⟩⟨ψ0|ψ1⟩⟨ψ1|) = |⟨ψ0|ψ1⟩|² = F(|ψ0⟩, |ψ1⟩)."

**Formalization Note.** `C_s` is `sOverlap`, the real part of the trace of `ρ0^s ρ1^{1−s}`
with `CFC.rpow` powers, defined for arbitrary operators; the middle expression
`Tr(|ψ0⟩⟨ψ0|ψ1⟩⟨ψ1|)` is the basis-sum trace of the product `ρ0 ρ1`, and its equality with
`|⟨ψ0|ψ1⟩|²` is stated in `ℂ`, so its imaginary part vanishes. The range `0 < s < 1` is the printed one and
cannot be widened: at `s = 0`, `C_0 = Tr ρ1 = 1`. -/
theorem eq_21 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ψ0 ψ1 : H) (hψ0 : ‖ψ0‖ = 1) (hψ1 : ‖ψ1‖ = 1) (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    sOverlap (pureState ψ0) (pureState ψ1) s =
        (basisOperatorTrace (pureState ψ0 * pureState ψ1)).re ∧
      basisOperatorTrace (pureState ψ0 * pureState ψ1) = ((‖inner ℂ ψ0 ψ1‖ ^ 2 : ℝ) : ℂ) ∧
      pureFidelity ψ0 (pureState ψ1) = ‖inner ℂ ψ0 ψ1‖ ^ 2 := by sorry

end SpedalieriQHT
